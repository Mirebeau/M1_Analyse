/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.W1p
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Théorème de Rademacher (`th:Rademacher`)

Caractérisation de `W^{1,∞}(Ω)` par les fonctions lipschitziennes bornées. Le théorème de
Rademacher de Mathlib (`LipschitzWith.ae_differentiableAt`) n'est pas utilisé directement : le
sens « lipschitzienne ⇒ `W^{1,∞}` » repose sur l'intégration par parties
`integral_lineDeriv_mul_eq` de son fichier ; le sens réciproque, sur la régularisation par
convolution et le prolongement de McShane.
-/

open MeasureTheory Set
open scoped ENNReal NNReal Distributions LineDeriv Convolution

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- `L^p(Ω) ⊆ L^1_loc(Ω)` pour `p ≥ 1` (copie de `w1p_locInt`, privé). -/
private lemma radA_locInt {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) : LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)

/-- Copie de `w1p_ofFun_apply` (privé). -/
private lemma radA_ofFun_apply {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) (ψ : 𝓓(Ω, ℝ)) :
    Distribution.ofFun Ω (f : ℝᵈ → ℝ) volume ⊤ ψ = ∫ x in (Ω : Set ℝᵈ), f x * ψ x := by
  rw [Distribution.ofFun_apply (radA_locInt f), setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [smul_eq_mul, mul_comm]
  · intro x hx
    simp [ψ.zero_on_compl hx]

/-- Sens « lipschitzienne bornée ⇒ `W^{1,∞}(Ω)` », pour tout ouvert `Ω` : prolongement de
McShane, puis intégration par parties de Mathlib (`integral_lineDeriv_mul_eq`). -/
private theorem radA_lip_mem (Ω : TopologicalSpace.Opens ℝᵈ) {v : ℝᵈ → ℝ} {K : ℝ≥0}
    (hv : LipschitzOnWith K v Ω) {C : ℝ} (hC : ∀ x ∈ Ω, |v x| ≤ C) :
    ∃ u : Sobolev1 Ω ∞, (u.val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v := by
  obtain ⟨g, hg, hvg⟩ := hv.extend_real
  set μ := volume.restrict (Ω : Set ℝᵈ)
  have hΩ := ae_restrict_mem (μ := volume) Ω.isOpen.measurableSet
  have hgv : g =ᵐ[μ] v := by
    filter_upwards [hΩ] with x hx
    exact (hvg hx).symm
  have hgL : MemLp g ∞ μ := by
    refine memLp_top_of_bound hg.continuous.aestronglyMeasurable C ?_
    filter_upwards [hΩ] with x hx
    rw [← hvg hx, Real.norm_eq_abs]
    exact hC x hx
  have hGL : ∀ i : Fin d,
      MemLp (fun x => lineDeriv ℝ g x (EuclideanSpace.single i (1 : ℝ))) ∞ μ :=
    fun i => hg.memLp_lineDeriv _
  let U : LpGrad Ω ∞ := WithLp.toLp ∞ (hgL.toLp g,
    WithLp.toLp ∞ (fun i => (hGL i).toLp _))
  have hU : U ∈ W1p Ω ∞ := by
    rw [mem_W1p]
    intro i
    ext ψ
    set e : ℝᵈ := EuclideanSpace.single i (1 : ℝ)
    rw [Distribution.lineDerivOp_eq_lineDerivCLM, Distribution.lineDerivCLM_apply,
      radA_ofFun_apply, radA_ofFun_apply]
    set Dψ : 𝓓(Ω, ℝ) := TestFunction.lineDerivCLM ℝ e ψ
    have hD : ∀ x, Dψ x = lineDeriv ℝ ψ x e := fun x =>
      TestFunction.lineDerivCLM_apply_of_le (by simp)
    have hψ : ∀ x ∉ (Ω : Set ℝᵈ), ψ x = 0 := fun x hx => ψ.zero_on_compl hx
    have hDψ : ∀ x ∉ (Ω : Set ℝᵈ), lineDeriv ℝ ψ x e = 0 := fun x hx => by
      rw [← hD]; exact Dψ.zero_on_compl hx
    have h1 : ∫ x in (Ω : Set ℝᵈ), U.fst x * Dψ x = ∫ x, g x * lineDeriv ℝ ψ x e := by
      refine (integral_congr_ae ?_).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set ℝᵈ))
          (f := fun x => g x * lineDeriv ℝ ψ x e) (fun x hx => by simp [hDψ x hx]))
      filter_upwards [hgL.coeFn_toLp] with x hx
      change (hgL.toLp g) x * Dψ x = _
      rw [hx, hD]
    have h2 : ∫ x in (Ω : Set ℝᵈ), U.snd i x * ψ x = ∫ x, lineDeriv ℝ g x e * ψ x := by
      refine (integral_congr_ae ?_).trans
        (setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set ℝᵈ))
          (f := fun x => lineDeriv ℝ g x e * ψ x) (fun x hx => by simp [hψ x hx]))
      filter_upwards [(hGL i).coeFn_toLp] with x hx
      change ((hGL i).toLp _) x * ψ x = _
      rw [hx]
    obtain ⟨Kψ, hKψ⟩ := ψ.contDiff.lipschitzWith_of_hasCompactSupport ψ.hasCompactSupport
      (by simp)
    rw [h1, h2, hg.integral_lineDeriv_mul_eq hKψ ψ.hasCompactSupport e, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [lineDeriv_neg]
    ring
  refine ⟨⟨U, hU⟩, ?_⟩
  exact (hgL.coeFn_toLp).trans hgv

private lemma radB_locInt (Ω : TopologicalSpace.Opens ℝᵈ)
    (f : Lp ℝ ∞ (volume.restrict (Ω : Set ℝᵈ))) :
    LocallyIntegrable ((Ω : Set ℝᵈ).indicator (f : ℝᵈ → ℝ)) volume :=
  ((memLp_indicator_iff_restrict Ω.isOpen.measurableSet).2 (Lp.memLp f)).locallyIntegrable
    le_top

private lemma radB_weak (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞) (ψ : 𝓓(Ω, ℝ))
    (i : Fin d) :
    ∫ x, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) *
        (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x =
      -∫ x, ψ x * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x := by
  have hW := mem_W1p.mp u.2 i
  have H := congrArg (fun T => T ψ) hW
  have hl : ∀ f : Lp ℝ ∞ (volume.restrict (Ω : Set ℝᵈ)), LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
    fun f => locallyIntegrableOn_of_locallyIntegrable_restrict
      ((Lp.memLp f).locallyIntegrable le_top)
  simp only at H
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply (hl _),
    Distribution.ofFun_apply (hl _)] at H
  have hd : ∀ x, (-∂_{EuclideanSpace.single i (1 : ℝ)} ψ) x =
      -fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    change -(∂_{EuclideanSpace.single i (1 : ℝ)} ψ) x = _
    rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ le_top]
  have h1 : ∀ x, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) *
      (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x =
      -((-∂_{EuclideanSpace.single i (1 : ℝ)} ψ) x • (u.val : ℝᵈ → ℝ) x) := by
    intro x
    by_cases hx : x ∈ (Ω : Set ℝᵈ)
    · rw [indicator_of_mem hx, hd, smul_eq_mul]
      ring
    · have h0 : (-∂_{EuclideanSpace.single i (1 : ℝ)} ψ) x = 0 :=
        (-∂_{EuclideanSpace.single i (1 : ℝ)} ψ).zero_on_compl hx
      rw [h0, zero_smul, neg_zero]
      rw [hd, neg_eq_zero] at h0
      rw [h0, zero_mul]
  have h2 : ∀ x, ψ x * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x =
      ψ x • (u.grad i : ℝᵈ → ℝ) x := by
    intro x
    by_cases hx : x ∈ (Ω : Set ℝᵈ)
    · rw [indicator_of_mem hx, smul_eq_mul]
    · have h0 : ψ x = 0 := ψ.zero_on_compl hx
      rw [h0, zero_mul, zero_smul]
  simp_rw [h1, h2, integral_neg]
  exact congrArg _ H

private lemma radB_sqrt_le (a : Fin d → ℝ) : √(∑ i, a i ^ 2) ≤ ∑ i, |a i| := by
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun i _ => abs_nonneg _, ?_⟩
  have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun i => |a i|)
    fun i _ => abs_nonneg _
  simpa only [sq_abs] using h

private lemma radB_cs (a w : Fin d → ℝ) :
    |∑ i, w i * a i| ≤ √(∑ i, w i ^ 2) * √(∑ i, a i ^ 2) := by
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => -w i) a
    simp only [neg_mul, Finset.sum_neg_distrib, neg_sq] at h
    linarith
  · exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ w a

private lemma radB_meas (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞) :
    AEStronglyMeasurable (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2))
      (volume.restrict (Ω : Set ℝᵈ)) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable
    (Finset.aestronglyMeasurable_fun_sum _ fun _ _ => (Lp.aestronglyMeasurable _).pow 2)

private lemma radB_finite (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞) :
    eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
      (volume.restrict (Ω : Set ℝᵈ)) ≠ ∞ := by
  have hS : MemLp (fun z => ∑ i, |(u.grad i : ℝᵈ → ℝ) z|) ∞ (volume.restrict (Ω : Set ℝᵈ)) :=
    memLp_finsetSum _ fun _ _ => (Lp.memLp _).abs
  refine (hS.of_le (radB_meas Ω u) (Filter.Eventually.of_forall fun z => ?_)).eLpNorm_ne_top
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)]
  exact radB_sqrt_le _

private lemma radB_bound (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞) :
    ∀ᵐ y ∂volume, ∀ w : ℝᵈ, |∑ i, w i * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) y| ≤
      (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
        (volume.restrict (Ω : Set ℝᵈ))).toReal * ‖w‖ := by
  set F := fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2) with hFdef
  have hF := ae_le_eLpNormEssSup (f := F) (μ := volume.restrict (Ω : Set ℝᵈ))
  rw [ae_restrict_iff' Ω.isOpen.measurableSet] at hF
  filter_upwards [hF] with y hy w
  have hM : 0 ≤ (eLpNorm F ∞ (volume.restrict (Ω : Set ℝᵈ))).toReal := ENNReal.toReal_nonneg
  by_cases hyΩ : y ∈ (Ω : Set ℝᵈ)
  · have h1 := hy hyΩ
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _), ← eLpNorm_exponent_top (radB_meas Ω u),
      ENNReal.ofReal_le_iff_le_toReal (radB_finite Ω u)] at h1
    simp only [indicator_of_mem hyΩ]
    have hw : ‖w‖ = √(∑ i, w i ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      simp
    refine (radB_cs _ _).trans ?_
    rw [← hw, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  · simp only [indicator_of_notMem hyΩ, mul_zero, Finset.sum_const_zero, abs_zero]
    positivity

private lemma radB_int (Ω : TopologicalSpace.Opens ℝᵈ) {f : ℝᵈ → ℝ}
    (hf : LocallyIntegrable f volume) (ψ : 𝓓(Ω, ℝ)) : Integrable (fun x => ψ x * f x) volume :=
  hf.integrable_smul_left_of_hasCompactSupport ψ.continuous ψ.hasCompactSupport

private lemma radB_lineDeriv (Ω : TopologicalSpace.Opens ℝᵈ) (ψ : 𝓓(Ω, ℝ)) (v x : ℝᵈ) :
    (∂_{v} ψ) x = fderiv ℝ ψ x v := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ le_top]

private lemma radB_weak_dir (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞) (ψ : 𝓓(Ω, ℝ))
    (w : ℝᵈ) :
    ∫ x, fderiv ℝ ψ x w * (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x =
      -∫ x, ψ x * ∑ i, w i * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x := by
  have hexp : ∀ x, fderiv ℝ ψ x w =
      ∑ i, w i * fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w]
    simp [map_sum, map_smul]
  have hI1 : ∀ i, Integrable (fun x => fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) *
      (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x) volume := by
    intro i
    have := radB_int Ω (radB_locInt Ω u.val) (∂_{EuclideanSpace.single i (1 : ℝ)} ψ)
    simpa only [radB_lineDeriv] using this
  have hI2 : ∀ i, Integrable (fun x => ψ x *
      (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x) volume :=
    fun i => radB_int Ω (radB_locInt Ω (u.grad i)) ψ
  calc ∫ x, fderiv ℝ ψ x w * (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x
      = ∫ x, ∑ i, w i * (fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) *
          (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x) := by
        simp_rw [hexp, Finset.sum_mul, mul_assoc]
    _ = ∑ i, w i * ∫ x, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) *
          (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) x := by
        rw [integral_finsetSum _ fun i _ => (hI1 i).const_mul (w i)]
        simp_rw [integral_const_mul]
    _ = ∑ i, w i * -∫ x, ψ x * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x := by
        simp_rw [radB_weak Ω u ψ]
    _ = -∫ x, ψ x * ∑ i, w i * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) x := by
        simp_rw [Finset.mul_sum]
        rw [integral_finsetSum _ fun i _ => ?_]
        · simp_rw [mul_left_comm (ψ _), integral_const_mul, mul_neg, Finset.sum_neg_distrib]
        · simp_rw [mul_left_comm (ψ _)]
          exact (hI2 i).const_mul (w i)

private lemma radB_fderiv_convol {k f : ℝᵈ → ℝ} (hk : ContDiff ℝ 1 k) (hkc : HasCompactSupport k)
    (hf : LocallyIntegrable f) (x v : ℝᵈ) :
    fderiv ℝ (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x v =
      ((fun t => fderiv ℝ k t v) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  rw [(hkc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hk hf x).fderiv,
    convolution_def, convolution_def]
  have hint := (hkc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL ℝᵈ) (hk.continuous_fderiv one_ne_zero) hf x
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

private lemma radB_conv (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞)
    (b : ContDiffBump (0 : ℝᵈ)) (z : ℝᵈ) (hz : Metric.closedBall z b.rOut ⊆ Ω) (w : ℝᵈ) :
    fderiv ℝ (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ)) z w =
      ∫ y, b.normed volume (z - y) *
        ∑ i, w i * (Ω : Set ℝᵈ).indicator (u.grad i : ℝᵈ → ℝ) y := by
  set φ := b.normed volume with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := b.contDiff_normed
  have hψc : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (z - y)) :=
    hφ.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport (fun y => φ (z - y)) :=
    b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft z)
  have hψt : tsupport (fun y => φ (z - y)) ⊆ (Ω : Set ℝᵈ) := by
    refine Subset.trans (closure_minimal ?_ Metric.isClosed_closedBall) hz
    intro y hy
    have h1 : z - y ∈ Function.support φ := hy
    rw [hφdef, b.support_normed_eq, Metric.mem_ball, dist_zero_right] at h1
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact h1.le
  let ψ : 𝓓(Ω, ℝ) := ⟨fun y => φ (z - y), hψc, hψs, hψt⟩
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdψ : ∀ y, fderiv ℝ ψ y w = - fderiv ℝ φ (z - y) w := by
    intro y
    have h0 := (hφd (z - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub z)
    have h1 : HasFDerivAt (fun y => φ (z - y))
        ((fderiv ℝ φ (z - y)).comp (-ContinuousLinearMap.id ℝ ℝᵈ)) y := h0
    have he : (⇑ψ : ℝᵈ → ℝ) = fun y => φ (z - y) := rfl
    rw [he, h1.fderiv]
    simp
  rw [radB_fderiv_convol (hφ.of_le (by simp)) b.hasCompactSupport_normed
    (radB_locInt Ω u.val), convolution_lsmul_swap]
  have H := radB_weak_dir Ω u ψ w
  simp_rw [hdψ, neg_mul, integral_neg, neg_inj] at H
  simp only [smul_eq_mul]
  exact H

private lemma radB_fderiv_le (Ω : TopologicalSpace.Opens ℝᵈ) (u : Sobolev1 Ω ∞)
    (b : ContDiffBump (0 : ℝᵈ)) (z : ℝᵈ) (hz : Metric.closedBall z b.rOut ⊆ Ω) :
    ‖fderiv ℝ (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ)) z‖ ≤
      (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
        (volume.restrict (Ω : Set ℝᵈ))).toReal := by
  refine ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg fun w => ?_
  set M := (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
    (volume.restrict (Ω : Set ℝᵈ))).toReal
  rw [radB_conv Ω u b z hz w]
  have hint : Integrable (fun y => b.normed volume (z - y) * (M * ‖w‖)) volume :=
    (b.integrable_normed.comp_sub_left z).mul_const _
  refine (norm_integral_le_of_norm_le hint ?_).trans_eq ?_
  · filter_upwards [radB_bound Ω u] with y hy
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (b.nonneg_normed _)]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hy w)
      (b.nonneg_normed _)
  · rw [integral_mul_const, integral_sub_left_eq_self (fun y => b.normed volume y) volume z,
      b.integral_normed, one_mul]

private lemma radB_lip_n (Ω : TopologicalSpace.Opens ℝᵈ) (hΩc : Convex ℝ (Ω : Set ℝᵈ))
    (u : Sobolev1 Ω ∞) (b : ℕ → ContDiffBump (0 : ℝᵈ))
    (hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0))
    (x : ℝᵈ) (hx : x ∈ Ω) (y : ℝᵈ) (hy : y ∈ Ω) :
    ∀ᶠ n in Filter.atTop,
      dist (((b n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ)) x)
        (((b n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ)) y) ≤
      (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
        (volume.restrict (Ω : Set ℝᵈ))).toReal * dist x y := by
  have hseg : segment ℝ x y ⊆ (Ω : Set ℝᵈ) := hΩc.segment_subset hx hy
  have hcomp : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨δ, hδ, hδΩ⟩ := hcomp.exists_cthickening_subset_open Ω.isOpen hseg
  filter_upwards [hb.eventually (gt_mem_nhds hδ)] with n hn
  have hball : ∀ z ∈ segment ℝ x y, Metric.closedBall z (b n).rOut ⊆ Ω := fun z hz =>
    ((Metric.closedBall_subset_closedBall hn.le).trans
      (Metric.closedBall_subset_cthickening hz δ)).trans hδΩ
  have hd : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ ((b n).normed volume
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ)) z :=
    fun z _ => ((b n).hasCompactSupport_normed.hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) ((b n).contDiff_normed) (radB_locInt Ω u.val)
        z).differentiableAt
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le hd
    (fun z hz => radB_fderiv_le Ω u (b n) z (hball z hz)) (right_mem_segment ℝ x y)
    (left_mem_segment ℝ x y)
  rwa [← dist_eq_norm, ← dist_eq_norm] at h

/-- **Th. `th:Rademacher`, cas convexe.** Si `Ω` est convexe (sans hypothèse de régularité),
toute `u ∈ W^{1,∞}(Ω)` admet un représentant `‖∇u‖_∞`-lipschitzien sur `Ω`, où
`‖∇u‖_∞ = ess sup_Ω |∇u|` (norme euclidienne du gradient).
Preuve (celle du cours, sans prolongement, et sans passer par le `th:injSurCrit`) :
`f_n := φ_n ⋆ u`, `φ_n` bosses normalisées de rayon `→ 0` ; près d'un segment `[x, y] ⊂ Ω`,
`∇f_n = φ_n ⋆ ∇u` (définition de la dérivée faible), donc `|∇f_n| ≤ ‖∇u‖_∞` et
`|f_n x - f_n y| ≤ ‖∇u‖_∞ |x - y|` ; `f_n → u` presque partout, donc `u` est
`‖∇u‖_∞`-lipschitzienne sur une partie de mesure pleine de `Ω`, et son prolongement de McShane
en est un représentant. -/
theorem th_Rademacher_convexe (Ω : TopologicalSpace.Opens ℝᵈ) (hΩc : Convex ℝ (Ω : Set ℝᵈ))
    (u : Sobolev1 Ω ∞) :
    ∃ v : ℝᵈ → ℝ, (u.val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v ∧
      ∀ x ∈ Ω, ∀ y ∈ Ω, |v x - v y| ≤
        (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
          (volume.restrict (Ω : Set ℝᵈ))).toReal * dist x y := by
  set M := (eLpNorm (fun z => √(∑ i, (u.grad i : ℝᵈ → ℝ) z ^ 2)) ∞
    (volume.restrict (Ω : Set ℝᵈ))).toReal with hMdef
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  set f0 := (Ω : Set ℝᵈ).indicator (u.val : ℝᵈ → ℝ) with hf0
  let b : ℕ → ContDiffBump (0 : ℝᵈ) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, 
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hb : Filter.Tendsto (fun n => (b n).rOut) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hK : ∀ᶠ n in Filter.atTop, (b n).rOut ≤ 2 * (b n).rIn :=
    Filter.Eventually.of_forall fun n => by
      change 1 / ((n : ℝ) + 1) ≤ 2 * (1 / (2 * ((n : ℝ) + 1)))
      apply le_of_eq
      field_simp
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) hb hK
    (radB_locInt Ω u.val)
  set A : Set ℝᵈ := {x | x ∈ (Ω : Set ℝᵈ) ∧ Filter.Tendsto (fun n =>
    ((b n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f0) x) Filter.atTop
      (nhds (f0 x))} with hAdef
  have hA : LipschitzOnWith ⟨M, hM⟩ f0 A := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    exact le_of_tendsto (hx.2.dist hy.2) (radB_lip_n Ω hΩc u b hb x hx.1 y hy.1)
  obtain ⟨g, hg, hEq⟩ := hA.extend_real
  refine ⟨g, ?_, fun x _ y _ => ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
    filter_upwards [hae] with x hx hxΩ
    rw [← hEq ⟨hxΩ, hx⟩, hf0, indicator_of_mem hxΩ]
  · rw [← Real.dist_eq]
    exact hg.dist_le_mul x y

/-- **Th. `th:Rademacher` (Rademacher).** Soit `Ω` ayant la propriété de prolongement de Sobolev
pour `p = ∞` (au lieu de « `Ω` régulier »). Une fonction `f` est dans `W^{1,∞}(Ω)` si et
seulement si elle admet un représentant borné et lipschitzien sur `Ω`. (Le sens réciproque vaut
pour tout ouvert `Ω`.)
Preuve : sens réciproque, intégration par parties pour les fonctions lipschitziennes (Mathlib) ;
sens direct, cas convexe appliqué au prolongement `P u ∈ W^{1,∞}(ℝ^d)`, le représentant
continu étant borné par `‖u‖_∞` sur `Ω` (borne presque partout et continuité). -/
theorem th_Rademacher (Ω : TopologicalSpace.Opens ℝᵈ) (hΩ : ProlongementSobolev Ω ∞)
    (f : ℝᵈ → ℝ) :
    (∃ u : Sobolev1 Ω ∞, (u.val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] f) ↔
      ∃ v : ℝᵈ → ℝ, (∃ K : ℝ≥0, LipschitzOnWith K v Ω) ∧ (∃ C : ℝ, ∀ x ∈ Ω, |v x| ≤ C) ∧
        f =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨P, hP⟩ := hΩ
    obtain ⟨v, hv, hlip⟩ := th_Rademacher_convexe ⊤ convex_univ (P u)
    set M := (eLpNorm (fun z => √(∑ i, ((P u).grad i : ℝᵈ → ℝ) z ^ 2)) ∞
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ))).toReal
    have hlip' : LipschitzWith M.toNNReal v := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.coe_toNNReal _ ENNReal.toReal_nonneg]
      exact hlip x trivial y trivial
    have hvΩ : (u.val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v := by
      have h1 : ((P u).val : ℝᵈ → ℝ) =ᵐ[volume] v := by
        simpa using hv
      exact (hP u).symm.trans (ae_restrict_of_ae h1)
    obtain ⟨C, hCdef⟩ : ∃ C, C = (eLpNorm (u.val : ℝᵈ → ℝ) ∞
        (volume.restrict (Ω : Set ℝᵈ))).toReal := ⟨_, rfl⟩
    have hCae : ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), |v x| ≤ C := by
      have hfin : eLpNorm (u.val : ℝᵈ → ℝ) ∞ (volume.restrict (Ω : Set ℝᵈ)) ≠ ⊤ :=
        (Lp.memLp u.val).eLpNorm_ne_top
      filter_upwards [hvΩ, ae_le_eLpNormEssSup (f := (u.val : ℝᵈ → ℝ))
        (μ := volume.restrict (Ω : Set ℝᵈ))] with x hx hb
      rw [← hx, hCdef, ← Real.norm_eq_abs, ← ENNReal.ofReal_le_iff_le_toReal hfin,
        ofReal_norm, eLpNorm_exponent_top]
      exacts [hb, Lp.aestronglyMeasurable _]
    refine ⟨v, ⟨_, hlip'.lipschitzOnWith⟩, ⟨C, fun x hx => ?_⟩, hu.symm.trans hvΩ⟩
    by_contra hlt
    have hopen : IsOpen ((Ω : Set ℝᵈ) ∩ {y | C < |v y|}) :=
      Ω.isOpen.inter (isOpen_lt continuous_const (continuous_abs.comp hlip'.continuous))
    have hpos := hopen.measure_pos (volume : Measure ℝᵈ) ⟨x, hx, not_le.1 hlt⟩
    have h0 : volume ((Ω : Set ℝᵈ) ∩ {y | C < |v y|}) = 0 := by
      have := (ae_restrict_iff' Ω.isOpen.measurableSet).1 hCae
      rw [ae_iff] at this
      refine measure_mono_null (fun y hy => ?_) this
      simp only [ not_forall, not_le]
      exact ⟨hy.1, hy.2⟩
    exact hpos.ne' h0
  · rintro ⟨v, ⟨K, hK⟩, ⟨C, hC⟩, hfv⟩
    obtain ⟨u, hu⟩ := radA_lip_mem Ω hK hC
    exact ⟨u, hu.trans hfv.symm⟩

end M1Analyse
