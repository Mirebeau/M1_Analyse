/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import M1Analyse.Sobolev.FrechetKolmogorov
import M1Analyse.Sobolev.InjSousCritiqueW1p
import M1Analyse.Sobolev.InjSurCritique

/-!
# §5.5 Injection compacte de Sobolev - théorème de Rellich (`subsec:injCompacte`)

Source : `Include/Sobolev.tex`, sous-section `subsec:injCompacte`.

Formalisés : `prop:interpLp` (avec `eLpNorm`), `prop:trans_grad_lp`, et `th:Rellich` en trois
théorèmes (cas sous-critique, critique, sur-critique), pour `p > 1` (et `p < ∞` dans le cas
sur-critique), sous l'hypothèse `Ω` borné et `ProlongementSobolevTout Ω` (au lieu de « `Ω` borné
régulier », \claudereport). Les espaces `W^{1,p}(Ω)` sont ceux de
`M1Analyse/Sobolev/W1p.lean`. `corol:Rellich` est dans `M1Analyse/Sobolev/RellichCorollaire.lean`.
`ex:nonLinMinH1` est dans `M1Analyse/Sobolev/MinNonLinH1.lean`, `rem:bouleW1pFerme` dans
`M1Analyse/Sobolev/BouleW1pFerme.lean`.
-/

open MeasureTheory
open scoped ENNReal

namespace M1Analyse

/-- **Prop. `prop:interpLp` (Inégalité d'interpolation `L^p`).** Soient `(X, μ)` un espace
mesuré, `f : X → ℝ` mesurable, `p₀, p₁ ∈ [1, ∞]` et `θ ∈ ]0, 1[`. Alors
`‖f‖_{p_θ} ≤ ‖f‖_{p₀}^{1-θ} ‖f‖_{p₁}^θ`, où `1/p_θ := (1-θ)/p₀ + θ/p₁`.
Remarque : l'hypothèse `p₀, p₁ ≥ 1` du cours est superflue (l'énoncé vaut pour
`p₀, p₁ ∈ [0, ∞]`). -/
theorem prop_interpLp {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : AEStronglyMeasurable f μ) {p₀ p₁ pθ : ℝ≥0∞} {θ : ℝ} (hθ₀ : 0 < θ) (hθ₁ : θ < 1)
    (hpθ : 1 / pθ = ENNReal.ofReal (1 - θ) / p₀ + ENNReal.ofReal θ / p₁) :
    eLpNorm f pθ μ ≤ eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
  have h1θ : 0 < 1 - θ := by linarith
  set a := p₀ * ENNReal.ofReal (1 / (1 - θ)) with ha
  set b := p₁ * ENNReal.ofReal (1 / θ) with hb
  have hinv : ∀ (q : ℝ≥0∞) (s : ℝ), 0 < s →
      (q * ENNReal.ofReal (1 / s))⁻¹ = ENNReal.ofReal s / q := by
    intro q s hs
    rw [ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top) (Or.inr (by simp [hs])),
      ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv, div_eq_mul_inv, mul_comm]
  have hT : ENNReal.HolderTriple a b pθ := by
    constructor
    rw [ha, hb, hinv _ _ h1θ, hinv _ _ hθ₀, ← hpθ, one_div]
  have hn : ∀ x, ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ = ‖f x‖ := by
    intro x
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num), sub_add_cancel, Real.rpow_one]
  calc eLpNorm f pθ μ = eLpNorm (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ) pθ μ := by
        simp only [hn]; exact (eLpNorm_norm f hf).symm
    _ ≤ eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) a μ * eLpNorm (fun x => ‖f x‖ ^ θ) b μ :=
        eLpNorm_smul_le_mul_eLpNorm (φ := fun x => ‖f x‖ ^ (1 - θ)) (f := fun x => ‖f x‖ ^ θ)
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
          (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
    _ = eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
        rw [eLpNorm_norm_rpow f hf h1θ, eLpNorm_norm_rpow f hf hθ₀, ha, hb, mul_assoc, mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          one_div_mul_cancel h1θ.ne', one_div_mul_cancel hθ₀.ne', ENNReal.ofReal_one, mul_one,
          mul_one]

section RellichW1p

open Set Filter Topology Metric
open scoped NNReal Convolution Distributions LineDeriv
open ContinuousLinearMap (lsmul)

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Accroissements finis sous forme intégrale, le long du segment `[x, x + h]`. -/
private lemma rellich_enorm_sub_le {w M : ℝᵈ → ℝ} (hw : ContDiff ℝ 1 w) {x h : ℝᵈ}
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ w (x + t • h) h‖ₑ ≤ ‖h‖ₑ * ‖M (x + t • h)‖ₑ) :
    ‖w (x + h) - w x‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖M (x + t • h)‖ₑ := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => w (x + t • h))
      (fderiv ℝ w (x + t • h) h) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add x
    exact ((hw.differentiable one_ne_zero) (x + t • h)).hasFDerivAt.comp_hasDerivAt t h1
  have hc : Continuous fun t : ℝ => fderiv ℝ w (x + t • h) h :=
    ((hw.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at heq
  rw [← heq, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  exact setLIntegral_mono' measurableSet_Ioc fun t ht => hb t (Ioc_subset_Icc_self ht)

/-- Cas régulier de `prop:trans_grad_lp`. -/
private lemma rellich_trans_smooth {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hpt : p ≠ ∞) {w M : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 1 w) (hM : Continuous M) {ω K : Set ℝᵈ} (hω : MeasurableSet ω)
    (hK : MeasurableSet K) (h : ℝᵈ) (hωK : ∀ x ∈ ω, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ K)
    (hb : ∀ y ∈ K, ‖fderiv ℝ w y h‖ₑ ≤ ‖h‖ₑ * ‖M y‖ₑ) :
    eLpNorm (fun x => w (x + h) - w x) p (volume.restrict ω) ≤
      ‖h‖ₑ * eLpNorm M p (volume.restrict K) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  set r := p.toReal with hr_def
  have hr1 : 1 ≤ r := by
    rw [hr_def, ← ENNReal.toReal_one]; exact ENNReal.toReal_mono hpt hp1
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  have hwc : Continuous w := hw.continuous
  have hΔ : Continuous fun x => w (x + h) - w x := by fun_prop
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hΔ.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hM.aestronglyMeasurable, ← hr_def]
  set F : ℝᵈ → ℝ → ℝ≥0∞ := fun x t => ‖M (x + t • h)‖ₑ ^ r with hF_def
  have hMc : Continuous fun z : ℝᵈ × ℝ => M (z.1 + z.2 • h) :=
    hM.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hF : Measurable (Function.uncurry F) := hMc.measurable.enorm.pow_const r
  have hhr : ‖h‖ₑ ^ r ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hr0.le enorm_ne_top
  have hI : volume (Ioc (0 : ℝ) 1) = 1 := by simp
  have hpw : ∀ x ∈ ω, ‖w (x + h) - w x‖ₑ ^ r ≤ ‖h‖ₑ ^ r * ∫⁻ t in Ioc (0 : ℝ) 1, F x t := by
    intro x hx
    have h1 := rellich_enorm_sub_le hw (M := M) (fun t ht => hb _ (hωK x hx t ht))
    have hbm : Measurable fun t : ℝ => ‖h‖ₑ * ‖M (x + t • h)‖ₑ :=
      ((hM.comp (continuous_const.add (continuous_id.smul continuous_const))).measurable.enorm
        ).const_mul _
    have h2 := lintegral_mul_rpow_le (volume.restrict (Ioc (0 : ℝ) 1)) hr1
      (a := fun _ => 1) aemeasurable_const hbm.aemeasurable
    simp only [one_mul, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
      hI, ENNReal.one_rpow] at h2
    calc ‖w (x + h) - w x‖ₑ ^ r
        ≤ (∫⁻ t in Ioc (0 : ℝ) 1, ‖h‖ₑ * ‖M (x + t • h)‖ₑ) ^ r := by gcongr
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1, (‖h‖ₑ * ‖M (x + t • h)‖ₑ) ^ r := h2
      _ = ‖h‖ₑ ^ r * ∫⁻ t in Ioc (0 : ℝ) 1, F x t := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
        exact lintegral_const_mul' _ _ hhr
  have hin : ∀ t ∈ Ioc (0 : ℝ) 1, ∫⁻ x in ω, F x t ≤ ∫⁻ y in K, ‖M y‖ₑ ^ r := by
    intro t ht
    calc ∫⁻ x in ω, F x t = ∫⁻ x in ω, K.indicator (fun y => ‖M y‖ₑ ^ r) (x + t • h) := by
          refine setLIntegral_congr_fun hω fun x hx => ?_
          rw [indicator_of_mem (hωK x hx t (Ioc_subset_Icc_self ht))]
      _ ≤ ∫⁻ x, K.indicator (fun y => ‖M y‖ₑ ^ r) (x + t • h) := setLIntegral_le_lintegral _ _
      _ = ∫⁻ y in K, ‖M y‖ₑ ^ r := by
          rw [lintegral_add_right_eq_self (fun y => K.indicator (fun y => ‖M y‖ₑ ^ r) y),
            lintegral_indicator hK]
  have htot : ∫⁻ x in ω, ‖w (x + h) - w x‖ₑ ^ r ≤ ‖h‖ₑ ^ r * ∫⁻ y in K, ‖M y‖ₑ ^ r := by
    calc ∫⁻ x in ω, ‖w (x + h) - w x‖ₑ ^ r
        ≤ ∫⁻ x in ω, ‖h‖ₑ ^ r * ∫⁻ t in Ioc (0 : ℝ) 1, F x t := setLIntegral_mono' hω hpw
      _ = ‖h‖ₑ ^ r * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in ω, F x t := by
          rw [lintegral_const_mul' _ _ hhr, lintegral_lintegral_swap hF.aemeasurable]
      _ ≤ ‖h‖ₑ ^ r * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in K, ‖M y‖ₑ ^ r := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hin) _
      _ = ‖h‖ₑ ^ r * ∫⁻ y in K, ‖M y‖ₑ ^ r := by
          rw [setLIntegral_const, hI, mul_one]
  calc (∫⁻ x in ω, ‖w (x + h) - w x‖ₑ ^ r) ^ (1 / r)
      ≤ (‖h‖ₑ ^ r * ∫⁻ y in K, ‖M y‖ₑ ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow htot (by positivity)
    _ = ‖h‖ₑ * (∫⁻ y in K, ‖M y‖ₑ ^ r) ^ (1 / r) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

private lemma rellich_locInt {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) : LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)

/-- Identité locale de la dérivée faible : si `k(x - ·)` est à support dans `Ω`, alors
`(∂ᵢ k) ⋆ ũ (x) = k ⋆ ∂ᵢũ (x)`, où `ũ` désigne le prolongement par `0` hors de `Ω`. -/
private lemma rellich_convol_weak {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : W1p Ω p) (i : Fin d) {k : ℝᵈ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (hkc : HasCompactSupport k) {x : ℝᵈ} (hx : tsupport (fun y => k (x - y)) ⊆ Ω) :
    ((fun t => fderiv ℝ k t (EuclideanSpace.single i 1)) ⋆
        (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ)) x =
      (k ⋆ (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).snd i : ℝᵈ → ℝ)) x := by
  set v : ℝᵈ := EuclideanSpace.single i 1
  have hψc : ContDiff ℝ (⊤ : ℕ∞) (fun y => k (x - y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  let ψ : 𝓓(Ω, ℝ) := ⟨fun y => k (x - y), hψc, hψs, hx⟩
  have hkd : Differentiable ℝ k := hk.differentiable (by simp)
  have hdψ : ∀ y, (∂_{v} ψ) y = - fderiv ℝ k (x - y) v := by
    intro y
    rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ le_top]
    have h0 := (hkd (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    have h1 : HasFDerivAt (fun y => k (x - y))
        ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ ℝᵈ)) y := h0
    have he : (⇑ψ : ℝᵈ → ℝ) = fun y => k (x - y) := rfl
    rw [he, h1.fderiv]
    simp
  have H := mem_W1p.mp u.2 i
  have H1 := congrArg (fun T => T ψ) H
  simp only at H1
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply (rellich_locInt _),
    Distribution.ofFun_apply (rellich_locInt _)] at H1
  rw [convolution_lsmul_swap, convolution_lsmul_swap]
  convert H1 using 2
  · funext y
    by_cases hy : y ∈ (Ω : Set ℝᵈ)
    · rw [indicator_of_mem hy,
        show ((-∂_{v} ψ : 𝓓(Ω, ℝ)) y) = -(∂_{v} ψ) y from rfl, hdψ, neg_neg]
    · rw [indicator_of_notMem hy, show ((-∂_{v} ψ : 𝓓(Ω, ℝ)) y) = -(∂_{v} ψ) y from rfl,
        TestFunction.zero_on_compl (∂_{v} ψ) hy]
      simp
  · funext y
    by_cases hy : y ∈ (Ω : Set ℝᵈ)
    · rw [indicator_of_mem hy]; rfl
    · rw [indicator_of_notMem hy, ψ.zero_on_compl hy]
      simp

private lemma rellich_sum_single (h : ℝᵈ) :
    h = ∑ i, h i • EuclideanSpace.single i (1 : ℝ) := by
  ext j; simp [Finset.sum_apply, Pi.single_apply]

/-- Cauchy–Schwarz : `|∑ hᵢ gᵢ| ≤ |h| (∑ gᵢ²)^{1/2}`. -/
private lemma rellich_abs_sum_le (h : ℝᵈ) (g : Fin d → ℝ) :
    |∑ i, h i * g i| ≤ ‖h‖ * √(∑ i, g i ^ 2) := by
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  refine Real.abs_le_sqrt ?_
  simpa only [Real.norm_eq_abs, sq_abs] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ h g

private lemma rellich_memLp_indicator {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞}
    {f : ℝᵈ → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set ℝᵈ))) :
    MemLp ((Ω : Set ℝᵈ).indicator f) p :=
  (memLp_indicator_iff_restrict Ω.isOpen.measurableSet).2 hf

/-- Norme euclidienne du gradient faible. -/
private noncomputable def rellich_gradNorm {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : LpGrad Ω p) : ℝᵈ → ℝ :=
  fun x => √(∑ i, ((u.snd i : ℝᵈ → ℝ) x) ^ 2)

private lemma rellich_memLp_gradNorm {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : LpGrad Ω p) :
    MemLp (rellich_gradNorm u) p (volume.restrict (Ω : Set ℝᵈ)) := by
  have hs : MemLp (fun x => ∑ i, |(u.snd i : ℝᵈ → ℝ) x|) p (volume.restrict (Ω : Set ℝᵈ)) :=
    memLp_finsetSum _ fun i _ => (Lp.memLp (u.snd i)).abs
  have hm : ∀ i, AEStronglyMeasurable (u.snd i : ℝᵈ → ℝ) (volume.restrict (Ω : Set ℝᵈ)) :=
    fun i => Lp.aestronglyMeasurable _
  refine hs.mono (by unfold rellich_gradNorm; fun_prop) (Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ ∑ i, |(u.snd i : ℝᵈ → ℝ) x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  simp only [rellich_gradNorm]
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg h0]
  refine Real.sqrt_le_iff.2 ⟨h0, ?_⟩
  simpa only [sq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      fun i _ => abs_nonneg ((u.snd i : ℝᵈ → ℝ) x)

/-- Dérivée d'une convolution `k ⋆ f`, `k ∈ C^1_c`, `f ∈ L^1_loc` :
`∂_v (k ⋆ f) = (∂_v k) ⋆ f`. -/
private lemma rellich_fderiv_convol {k f : ℝᵈ → ℝ} (hk : ContDiff ℝ 1 k)
    (hkc : HasCompactSupport k) (hf : LocallyIntegrable f) (x v : ℝᵈ) :
    fderiv ℝ (k ⋆ f) x v = ((fun t => fderiv ℝ k t v) ⋆ f) x := by
  rw [(hkc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hk hf x).fderiv, convolution_def,
    convolution_def]
  have hint := (hkc.fderiv ℝ).convolutionExists_left ((lsmul ℝ ℝ).precompL ℝᵈ)
    (hk.continuous_fderiv one_ne_zero) hf x
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

/-- Majoration du gradient de `k ⋆ ũ` (`k ≥ 0`) en un point `y` tel que `k(y - ·)` est à
support dans `Ω` : `|∇(k ⋆ ũ)(y) · h| ≤ |h| (k ⋆ |∇u|~)(y)`. -/
private lemma rellich_fderiv_bound {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : W1p Ω p) {k : ℝᵈ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k)
    (hk0 : ∀ x, 0 ≤ k x) {y : ℝᵈ} (hy : tsupport (fun t => k (y - t)) ⊆ Ω) (h : ℝᵈ) :
    ‖fderiv ℝ (k ⋆ (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ)) y h‖ₑ ≤
      ‖h‖ₑ * ‖(k ⋆ (Ω : Set ℝᵈ).indicator (rellich_gradNorm (u : LpGrad Ω p))) y‖ₑ := by
  set F := (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) with hF_def
  set G : Fin d → ℝᵈ → ℝ := fun i => (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).snd i : ℝᵈ → ℝ)
    with hG_def
  set N := (Ω : Set ℝᵈ).indicator (rellich_gradNorm (u : LpGrad Ω p)) with hN_def
  have hp1 : 1 ≤ p := Fact.out
  have hFl : LocallyIntegrable F :=
    (rellich_memLp_indicator (Lp.memLp _)).locallyIntegrable hp1
  have hGl : ∀ i, LocallyIntegrable (G i) := fun i =>
    (rellich_memLp_indicator (Lp.memLp _)).locallyIntegrable hp1
  have hNl : LocallyIntegrable N :=
    (rellich_memLp_indicator (rellich_memLp_gradNorm _)).locallyIntegrable hp1
  have hGi : ∀ i, Integrable (fun t => k (y - t) * G i t) := fun i =>
    ((hkc.convolutionExists_left (lsmul ℝ ℝ) hk.continuous (hGl i)) y).integrable_swap
  have hNi : Integrable (fun t => k (y - t) * N t) :=
    ((hkc.convolutionExists_left (lsmul ℝ ℝ) hk.continuous hNl) y).integrable_swap
  have hd : ∀ i, fderiv ℝ (k ⋆ F) y (EuclideanSpace.single i 1) =
      ∫ t, k (y - t) * G i t := fun i => by
    rw [rellich_fderiv_convol (hk.of_le (by simp)) hkc hFl, rellich_convol_weak u i hk hkc hy,
      convolution_lsmul_swap]
    rfl
  have he : fderiv ℝ (k ⋆ F) y h = ∫ t, k (y - t) * ∑ i, h i * G i t := by
    conv_lhs => rw [rellich_sum_single h]
    simp only [map_sum, map_smul, smul_eq_mul, hd]
    calc ∑ i, h i * ∫ t, k (y - t) * G i t = ∑ i, ∫ t, h i * (k (y - t) * G i t) :=
          Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
      _ = ∫ t, ∑ i, h i * (k (y - t) * G i t) :=
          (integral_finsetSum _ fun i _ => (hGi i).const_mul (h i)).symm
      _ = ∫ t, k (y - t) * ∑ i, h i * G i t := by
          congr 1; funext t
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  have hpt : ∀ t, ‖k (y - t) * ∑ i, h i * G i t‖ ≤ ‖h‖ * (k (y - t) * N t) := by
    intro t
    rw [norm_mul, Real.norm_of_nonneg (hk0 _), mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (hk0 _)
    by_cases ht : t ∈ (Ω : Set ℝᵈ)
    · simp only [G, N, indicator_of_mem ht, rellich_gradNorm, Real.norm_eq_abs]
      exact rellich_abs_sum_le h _
    · simp [G, N, indicator_of_notMem ht]
  have hM : (k ⋆ N) y = ∫ t, k (y - t) * N t := by rw [convolution_lsmul_swap]; rfl
  rw [← enorm_norm h, ← enorm_mul, enorm_le_iff_norm_le, he, hM]
  refine (norm_integral_le_of_norm_le (hNi.const_mul ‖h‖) (ae_of_all _ hpt)).trans ?_
  rw [integral_const_mul]
  exact Real.le_norm_self _

/-- **Prop. `prop:trans_grad_lp`.** Pour `Ω` ouvert, `p ∈ [1, ∞[`, `u ∈ W^{1,p}(Ω)`, `h ∈ ℝ^d` et
`ω` compact avec `ω + B'(0, |h|) ⊂ Ω` : `‖u(· + h) - u‖_{L^p(ω)} ≤ |h| ‖ |∇u| ‖_{L^p(Ω)}`
(racine `p`-ième de `eq:uhdup`), où `|∇u| = (∑ᵢ (∂ᵢu)²)^{1/2}`.
Preuve : cas lisse comme dans le cours (accroissements finis, Jensen, Fubini) ; le passage à
`u ∈ W^{1,p}(Ω)` se fait par régularisation locale `ρ_ε ⋆ u` près de `ω + B'(0, |h|)`, avec
`∇(ρ_ε ⋆ u) = ρ_ε ⋆ ∇u` (identité de la dérivée faible) et `‖ρ_ε ⋆ |∇u|‖_p ≤ ‖|∇u|‖_p`. -/
theorem prop_trans_grad_lp (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (u : Sobolev1 Ω p) (h : ℝᵈ) {ω : Set ℝᵈ} (hω : IsCompact ω)
    (hωh : cthickening ‖h‖ ω ⊆ Ω) :
    eLpNorm (fun x => u.val (x + h) - u.val x) p (volume.restrict ω) ≤
      ‖h‖ₑ * eLpNorm (fun x => √(∑ i, (u.grad i x) ^ 2)) p (volume.restrict (Ω : Set ℝᵈ)) := by
  simp only [Sobolev1.val_def, Sobolev1.grad_def]
  have hp1 : 1 ≤ p := Fact.out
  set K := cthickening ‖h‖ ω with hK_def
  have hKc : IsCompact K := hω.cthickening
  obtain ⟨δ, hδ0, hδ⟩ := hKc.exists_cthickening_subset_open Ω.isOpen hωh
  let χ : ContDiffBump (0 : ℝᵈ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  set ρ : ℝᵈ → ℝ := χ.normed volume with hρ_def
  have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := χ.contDiff_normed
  have hρc : HasCompactSupport ρ := χ.hasCompactSupport_normed
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => χ.nonneg_normed x
  have hρ1 : ∫ x, ρ x = 1 := χ.integral_normed
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hρs : Function.support ρ ⊆ closedBall 0 1 := by
    rw [hρ_def, χ.support_normed_eq]; exact ball_subset_closedBall
  set F := (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) with hF_def
  set N := (Ω : Set ℝᵈ).indicator (rellich_gradNorm (u : LpGrad Ω p)) with hN_def
  have hF : MemLp F p := rellich_memLp_indicator (Lp.memLp _)
  have hN : MemLp N p := rellich_memLp_indicator (rellich_memLp_gradNorm _)
  have hFl : LocallyIntegrable F := hF.locallyIntegrable hp1
  have hNl : LocallyIntegrable N := hN.locallyIntegrable hp1
  have hk : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (noyauEps ρ ε) := fun ε =>
    contDiff_const.mul (hρ.comp (contDiff_const_smul _))
  have hkc : ∀ ε, 0 < ε → HasCompactSupport (noyauEps ρ ε) := fun ε hε =>
    (hρc.comp_smul (inv_ne_zero hε.ne')).mul_left
  have hωK : ∀ x ∈ ω, ∀ t ∈ Icc (0 : ℝ) 1, x + t • h ∈ K := by
    intro x hx t ht
    refine mem_cthickening_of_dist_le (x + t • h) x ‖h‖ ω hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg h, ht.2]
  -- Estimation pour la régularisée `ρ_ε ⋆ ũ`, `ε < δ`.
  have key : ∀ ε, 0 < ε → ε < δ →
      eLpNorm (fun x => (noyauEps ρ ε ⋆ F) (x + h) - (noyauEps ρ ε ⋆ F) x) p
        (volume.restrict ω) ≤ ‖h‖ₑ * eLpNorm N p := by
    intro ε hε hεδ
    have hw : ContDiff ℝ 1 (noyauEps ρ ε ⋆ F) :=
      (hkc ε hε).contDiff_convolution_left (lsmul ℝ ℝ) ((hk ε).of_le (by simp)) hFl
    have hM : Continuous (noyauEps ρ ε ⋆ N) :=
      (hkc ε hε).continuous_convolution_left (lsmul ℝ ℝ) (hk ε).continuous hNl
    refine (rellich_trans_smooth hp1 hp hw hM hω.measurableSet hKc.measurableSet h hωK
      fun y hy => ?_).trans ?_
    · refine rellich_fderiv_bound u (hk ε) (hkc ε hε) (noyauEps_nonneg hρ0 hε) ?_ h
      refine (closure_minimal (fun t ht => ?_) isClosed_closedBall).trans
        ((closedBall_subset_cthickening hy ε).trans
          ((cthickening_mono hεδ.le K).trans hδ))
      have := norm_le_of_noyauEps_ne_zero hρs hε ht
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact this
    · gcongr
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      refine ((prop_convolLp hp1 (integrable_noyauEps hρi hε) hN).2.2).trans ?_
      have h1 : eLpNorm (noyauEps ρ ε) 1 = 1 := by
        rw [eLpNorm_one_eq_lintegral_enorm (integrable_noyauEps hρi hε).aestronglyMeasurable,
          lintegral_congr fun x => Real.enorm_of_nonneg (noyauEps_nonneg hρ0 hε x),
          ← ofReal_integral_eq_lintegral_ofReal (integrable_noyauEps hρi hε)
            (ae_of_all _ (noyauEps_nonneg hρ0 hε)), integral_noyauEps hε, hρ1, ENNReal.ofReal_one]
      rw [h1, one_mul, hN_def, eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet]
  -- Passage à la limite `ε → 0⁺`.
  have hL : eLpNorm (fun x => (u : LpGrad Ω p).fst (x + h) - (u : LpGrad Ω p).fst x) p
      (volume.restrict ω) = eLpNorm (fun x => F (x + h) - F x) p (volume.restrict ω) := by
    refine eLpNorm_congr_ae ((ae_restrict_mem hω.measurableSet).mono fun x hx => ?_)
    have h1 : x + h ∈ (Ω : Set ℝᵈ) := hωh (by simpa using hωK x hx 1 ⟨zero_le_one, le_rfl⟩)
    have h2 : x ∈ (Ω : Set ℝᵈ) := hωh (by simpa using hωK x hx 0 ⟨le_rfl, zero_le_one⟩)
    simp only [hF_def, indicator_of_mem h1, indicator_of_mem h2]
  rw [hL]
  set B := ‖h‖ₑ * eLpNorm (fun x => √(∑ i, ((u : LpGrad Ω p).snd i x) ^ 2)) p
    (volume.restrict (Ω : Set ℝᵈ)) with hB_def
  have hNB : ‖h‖ₑ * eLpNorm N p = B := by
    rw [hN_def, eLpNorm_indicator_eq_eLpNorm_restrict Ω.isOpen.measurableSet]; rfl
  have hmp := measurePreserving_add_right (volume : Measure ℝᵈ) h
  have hbd : ∀ ε, 0 < ε → ε < δ →
      eLpNorm (fun x => F (x + h) - F x) p (volume.restrict ω) ≤
        2 * moduleTransl p F ε + B := by
    intro ε hε hεδ
    set w := noyauEps ρ ε ⋆ F with hw_def
    have hwc : Continuous w :=
      (hkc ε hε).continuous_convolution_left (lsmul ℝ ℝ) (hk ε).continuous hFl
    have hFw : AEStronglyMeasurable (F - w) volume :=
      hF.aestronglyMeasurable.sub hwc.aestronglyMeasurable
    have hdec : (fun x => F (x + h) - F x) =
        (fun x => (F - w) (x + h)) + (fun x => w (x + h) - w x) + (w - F) := by
      funext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
    have hT1 : eLpNorm (fun x => (F - w) (x + h)) p (volume.restrict ω) ≤ moduleTransl p F ε := by
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      have : (fun x => (F - w) (x + h)) = (F - w) ∘ (fun x => x + h) := rfl
      rw [this, eLpNorm_comp_measurePreserving hFw hmp]
      exact prop_convolApprox_le hρ0 hρi hρs hρ1 hp1 hp hF hε
    have hT3 : eLpNorm (w - F) p (volume.restrict ω) ≤ moduleTransl p F ε := by
      refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [eLpNorm_sub_comm]
      exact prop_convolApprox_le hρ0 hρi hρs hρ1 hp1 hp hF hε
    rw [hdec, two_mul, ← hNB]
    refine (eLpNorm_add_le (f := (fun x => (F - w) (x + h)) + fun x => w (x + h) - w x)
      (g := w - F) hp1).trans ?_
    refine (add_le_add (eLpNorm_add_le (f := fun x => (F - w) (x + h))
      (g := fun x => w (x + h) - w x) hp1) le_rfl).trans ?_
    calc eLpNorm (fun x => (F - w) (x + h)) p (volume.restrict ω) +
          eLpNorm (fun x => w (x + h) - w x) p (volume.restrict ω) +
          eLpNorm (w - F) p (volume.restrict ω)
        ≤ moduleTransl p F ε + ‖h‖ₑ * eLpNorm N p volume + moduleTransl p F ε := by
          gcongr
          exact key ε hε hεδ
      _ = moduleTransl p F ε + moduleTransl p F ε + ‖h‖ₑ * eLpNorm N p volume := by ring
  have hlim : Tendsto (fun ε => 2 * moduleTransl p F ε + B) (𝓝[>] 0) (𝓝 B) := by
    have := ((ENNReal.Tendsto.const_mul (prop_convolApprox_tendsto hp1 hp hF)
      (Or.inr ENNReal.ofNat_ne_top)).add_const B : Tendsto _ _ (𝓝 (2 * 0 + B)))
    rwa [mul_zero, zero_add] at this
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hδ0] with ε hε
  exact hbd ε hε.1 hε.2

/-- Propriété de prolongement de Sobolev pour tous les exposants `p ∈ [1, ∞]` : ce que
`th:prolSobolev` fournit pour un ouvert régulier. Hypothèse de `th:Rellich` (décision de
l'auteur), à la place de « `Ω` borné régulier » (avec `Ω` borné). -/
def ProlongementSobolevTout (Ω : TopologicalSpace.Opens ℝᵈ) : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], ProlongementSobolev Ω p

/-! ### Cas sous-critique -/

/-- Translation des égalités presque partout. -/
private lemma rellich_ae_comp_sub {Ω : Set ℝᵈ} {f g : ℝᵈ → ℝ} (hfg : f =ᵐ[volume.restrict Ω] g)
    (hΩ : MeasurableSet Ω) {K : Set ℝᵈ} (hK : MeasurableSet K) (h : ℝᵈ)
    (hKh : ∀ x ∈ K, x - h ∈ Ω) :
    (fun x => f (x - h)) =ᵐ[volume.restrict K] fun x => g (x - h) := by
  rw [EventuallyEq, ae_restrict_iff' hΩ] at hfg
  have := (measurePreserving_sub_right (volume : Measure ℝᵈ) h).quasiMeasurePreserving.ae hfg
  filter_upwards [ae_restrict_of_ae this, ae_restrict_mem hK] with x hx hxK
  exact hx (hKh x hxK)

private lemma rellich_fst_le {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v : LpGrad Ω p) : eLpNorm (v.fst : ℝᵈ → ℝ) p (volume.restrict (Ω : Set ℝᵈ)) ≤ ‖v‖ₑ := by
  rw [← Lp.enorm_def, enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
  exact WithLp.nnnorm_fst_le _ v

private lemma rellich_snd_le {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v : LpGrad Ω p) (i : Fin d) :
    eLpNorm (v.snd i : ℝᵈ → ℝ) p (volume.restrict (Ω : Set ℝᵈ)) ≤ ‖v‖ₑ := by
  rw [← Lp.enorm_def, enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe]
  exact (PiLp.nnnorm_apply_le _ i).trans (WithLp.nnnorm_snd_le _ v)

/-- `‖ |∇u| ‖_p ≤ d ‖u‖_{W^{1,p}}`. -/
private lemma rellich_gradNorm_le {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (v : LpGrad Ω p) :
    eLpNorm (rellich_gradNorm v) p (volume.restrict (Ω : Set ℝᵈ)) ≤ d * ‖v‖ₑ := by
  have hm : ∀ i, AEStronglyMeasurable (v.snd i : ℝᵈ → ℝ) (volume.restrict (Ω : Set ℝᵈ)) :=
    fun i => Lp.aestronglyMeasurable _
  calc eLpNorm (rellich_gradNorm v) p (volume.restrict (Ω : Set ℝᵈ))
      ≤ eLpNorm (∑ i, fun x => ‖(v.snd i : ℝᵈ → ℝ) x‖) p (volume.restrict (Ω : Set ℝᵈ)) := by
        refine eLpNorm_mono (by unfold rellich_gradNorm; fun_prop) fun x => ?_
        have h0 : 0 ≤ ∑ i, ‖(v.snd i : ℝᵈ → ℝ) x‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
        simp only [rellich_gradNorm, Finset.sum_apply]
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg h0]
        refine Real.sqrt_le_iff.2 ⟨h0, ?_⟩
        simpa only [Real.norm_eq_abs, sq_abs] using
          Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
            fun i _ => norm_nonneg ((v.snd i : ℝᵈ → ℝ) x)
    _ ≤ ∑ i, eLpNorm (fun x => ‖(v.snd i : ℝᵈ → ℝ) x‖) p (volume.restrict (Ω : Set ℝᵈ)) :=
        eLpNorm_sum_le Fact.out
    _ ≤ ∑ _i : Fin d, ‖v‖ₑ := Finset.sum_le_sum fun i _ => by
        rw [eLpNorm_norm _ (hm i)]; exact rellich_snd_le v i
    _ = d * ‖v‖ₑ := by simp

/-- Exposant d'interpolation entre `1/2` et `p*` pour `q ∈ [1, p*[`. -/
private lemma rellich_exists_theta {q pstar : ℝ≥0∞} (hq1 : 1 ≤ q) (hpst : pstar ≠ ∞)
    (hq : q < pstar) : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      1 / q = ENNReal.ofReal (1 - θ) / 2⁻¹ + ENNReal.ofReal θ / pstar := by
  have hqt : q ≠ ∞ := hq.ne_top
  have hq0r : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq1).ne' hqt
  have hqps : q.toReal < pstar.toReal := ENNReal.toReal_strict_mono hpst hq
  have hps0r : 0 < pstar.toReal := hq0r.trans hqps
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 / q.toReal := ⟨_, rfl⟩
  obtain ⟨b, hb_def⟩ : ∃ b : ℝ, b = 1 / pstar.toReal := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb_def]; positivity
  have hab : b < a := by rw [ha_def, hb_def]; exact one_div_lt_one_div_of_lt hq0r hqps
  have ha1 : a ≤ 1 := by
    rw [ha_def, div_le_one hq0r, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hqt hq1
  refine ⟨(2 - a) / (2 - b), div_pos (by linarith) (by linarith),
    (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  have hθb : (2 - a) / (2 - b) * (2 - b) = 2 - a := div_mul_cancel₀ _ (by linarith)
  have hθ0 : 0 ≤ (2 - a) / (2 - b) := div_nonneg (by linarith) (by linarith)
  have hθ1 : (2 - a) / (2 - b) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  rw [← ENNReal.ofReal_toReal hqt, ← ENNReal.ofReal_toReal hpst, div_eq_mul_inv _ 2⁻¹,
    inv_inv, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by linarith),
    ← ENNReal.ofReal_div_of_pos hps0r, ← ENNReal.ofReal_add (by nlinarith) (by positivity),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_div_of_pos hq0r]
  congr 1
  rw [← ha_def, div_eq_mul_one_div ((2 - a) / (2 - b)), ← hb_def]
  linarith

/-- Régularité sous translation dans `L^q(K)` (preuve de `th:Rellich`, sous-critique) :
interpolation entre `L^{1/2}(K)` (Hölder et `prop:trans_grad_lp`) et `L^{p*}(K)`. -/
private lemma rellich_transl {Ω : TopologicalSpace.Opens ℝᵈ} {p pstar q : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ∞) (hps1 : 1 ≤ pstar) {C : ℝ≥0}
    (hCu : ∀ u : W1p Ω p, ‖u‖ ≤ 1 →
      eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ≤ C)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hpθ : 1 / q = ENNReal.ofReal (1 - θ) / 2⁻¹ + ENNReal.ofReal θ / pstar)
    {K : Set ℝᵈ} (hKc : IsCompact K) (hKΩ : K ⊆ Ω) (u : W1p Ω p) (hu : ‖u‖ ≤ 1) (h : ℝᵈ)
    (hKh : cthickening ‖h‖ K ⊆ Ω) :
    eLpNorm (fun x => (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) x -
        (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) (x - h)) q (volume.restrict K) ≤
      ((‖h‖₊ : ℝ≥0∞) * (d * volume K ^ (1 / (2⁻¹ : ℝ≥0∞).toReal - 1 / p.toReal))) ^ (1 - θ) *
        (2 * C) ^ θ := by
  have hp1 : 1 ≤ p := Fact.out
  have hKm : MeasurableSet K := hKc.measurableSet
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  have hu1 : ‖u‖ₑ ≤ 1 := by rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 hu
  obtain ⟨g, hg_def⟩ : ∃ g : ℝᵈ → ℝ, g = ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) := ⟨_, rfl⟩
  obtain ⟨F, hF_def⟩ : ∃ F : ℝᵈ → ℝ, F = (Ω : Set ℝᵈ).indicator g := ⟨_, rfl⟩
  rw [← hg_def, ← hF_def]
  have hKh' : ∀ x ∈ K, x - h ∈ (Ω : Set ℝᵈ) := fun x hx =>
    hKh (mem_cthickening_of_dist_le _ x _ _ hx (by rw [dist_eq_norm, sub_sub_cancel_left,
      norm_neg]))
  have hFm : AEStronglyMeasurable F volume := by
    rw [hF_def, hg_def]
    exact (aestronglyMeasurable_indicator_iff hΩm).2 (Lp.aestronglyMeasurable _)
  have hmp := measurePreserving_sub_right (volume : Measure ℝᵈ) h
  obtain ⟨Δ, hΔ_def⟩ : ∃ Δ : ℝᵈ → ℝ, Δ = fun x => F x - F (x - h) := ⟨_, rfl⟩
  rw [← hΔ_def]
  have hΔm : AEStronglyMeasurable Δ (volume.restrict K) :=
    hΔ_def ▸ (hFm.sub (hFm.comp_measurePreserving hmp)).restrict
  -- (a) estimation `L^p` (`prop:trans_grad_lp`)
  have hEp : eLpNorm Δ p (volume.restrict K) ≤ ‖h‖ₑ * d := by
    have H := prop_trans_grad_lp Ω hpt u (-h) hKc (by rwa [norm_neg])
    have he : Δ =ᵐ[volume.restrict K] -fun x => g (x + -h) - g x := by
      filter_upwards [ae_restrict_mem hKm] with x hx
      simp only [hΔ_def, hF_def, Pi.neg_apply, indicator_of_mem (hKΩ hx),
        indicator_of_mem (hKh' x hx), ← sub_eq_add_neg]
      ring
    rw [eLpNorm_congr_ae he, eLpNorm_neg, hg_def]
    refine H.trans ?_
    rw [enorm_neg]
    gcongr
    exact (rellich_gradNorm_le (u : LpGrad Ω p)).trans (mul_le_of_le_one_right' hu1)
  -- (b) estimation `L^{1/2}` (Hölder sur `K`)
  have hE0 : eLpNorm Δ 2⁻¹ (volume.restrict K) ≤
      ‖h‖ₑ * d * volume K ^ (1 / (2⁻¹ : ℝ≥0∞).toReal - 1 / p.toReal) := by
    have h2p : (2⁻¹ : ℝ≥0∞) ≤ p := (ENNReal.inv_le_one.2 one_le_two).trans hp1
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2p hΔm).trans ?_
    rw [Measure.restrict_apply_univ]
    gcongr
  -- (c) estimation `L^{p*}`
  have hEs : eLpNorm Δ pstar (volume.restrict K) ≤ 2 * C := by
    have hFs : eLpNorm F pstar volume ≤ C := by
      rw [hF_def, eLpNorm_indicator_eq_eLpNorm_restrict hΩm, hg_def]; exact hCu u hu
    rw [hΔ_def]
    refine (eLpNorm_sub_le hps1).trans ?_
    rw [two_mul]
    gcongr
    · exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hFs
    · refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      have : (fun x => F (x - h)) = F ∘ (fun x => x - h) := rfl
      rw [this, eLpNorm_comp_measurePreserving hFm hmp]
      exact hFs
  -- (d) interpolation
  refine (prop_interpLp (volume.restrict K) hΔm hθ0 hθ1 hpθ).trans ?_
  rw [enorm_eq_nnnorm] at hE0
  rw [← mul_assoc]
  gcongr

/-- **Th. `th:Rellich` (Rellich), cas sous-critique.** Soient `Ω` borné ayant la propriété de
prolongement de Sobolev, `1 < p < d`, `1/p* = 1/p - 1/d` et `q ∈ [1, p*[`. Tout `u ∈ W^{1,p}(Ω)`
est dans `L^q(Ω)`, et la boule unité fermée de `W^{1,p}(Ω)` est précompacte dans `L^q(Ω)`.
Preuve (différente du cours) : critères de Fréchet–Kolmogorov comme dans le cours, mais
l'interpolation se fait entre les exposants `1/2` et `p*` (au lieu de `1` et `p*`), ce qui
évite `W^{1,1}` et le cas dégénéré `q = 1`.
Dépend de l'axiome de Young faible (via `corol_injSousCritOm`). -/
theorem th_Rellich_sousCritique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p pstar q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hpd : p < d)
    (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹) (hq : q < pstar) :
    (∀ u : Sobolev1 Ω p, MemLp (u.val : ℝᵈ → ℝ) q (volume.restrict (Ω : Set ℝᵈ))) ∧
      TotallyBounded {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω p, ‖u‖ ≤ 1 ∧
        (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val} := by
  simp only [Sobolev1.val_def]
  have hpt : p ≠ ∞ := (hpd.trans (ENNReal.natCast_lt_top d)).ne
  have hqt : q ≠ ∞ := hq.ne_top
  have hq1 : 1 ≤ q := Fact.out
  have hps0 : pstar⁻¹ ≠ 0 := by
    rw [hpstar]; exact (tsub_pos_of_lt (ENNReal.inv_lt_inv.2 hpd)).ne'
  have hpst : pstar ≠ ∞ := fun h => hps0 (by simp [h])
  have hps1 : 1 ≤ pstar := hq1.trans hq.le
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  have hΩf : volume (Ω : Set ℝᵈ) ≠ ∞ := hΩb.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) := isFiniteMeasure_restrict.2 hΩf
  obtain ⟨C, hC⟩ := corol_injSousCritOm Ω hp hpd hpstar (hΩ p)
  have hu1 : ∀ u : W1p Ω p, ‖u‖ ≤ 1 → ‖u‖ₑ ≤ 1 := fun u hu => by
    rw [← ofReal_norm]; exact ENNReal.ofReal_le_one.2 hu
  have hCu : ∀ u : W1p Ω p, ‖u‖ ≤ 1 →
      eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ≤ C :=
    fun u hu => (hC u).2.trans (mul_le_of_le_one_right' (hu1 u hu))
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = 1 / q.toReal - 1 / pstar.toReal := ⟨_, rfl⟩
  have hq0r : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hq1).ne' hqt
  have hqps : q.toReal < pstar.toReal := ENNReal.toReal_strict_mono hpst hq
  have hs0 : 0 < s := hs_def ▸ sub_pos.2 (one_div_lt_one_div_of_lt hq0r hqps)
  have hloc : ∀ u : W1p Ω p, ‖u‖ ≤ 1 → ∀ S ⊆ (Ω : Set ℝᵈ),
      eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) q (volume.restrict S) ≤ C * volume S ^ s := by
    intro u hu S hS
    have hm : AEStronglyMeasurable ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) (volume.restrict S) :=
      (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hS le_rfl)
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq.le hm).trans ?_
    rw [Measure.restrict_apply_univ, hs_def]
    gcongr
    exact (eLpNorm_mono_measure _ (Measure.restrict_mono hS le_rfl)).trans (hCu u hu)
  refine ⟨fun u => (hC u).1.mono_exponent hq.le, ?_⟩
  obtain ⟨θ, hθ0, hθ1, hpθ⟩ := rellich_exists_theta hq1 hpst hq
  refine th_FrechetKolmogorov Ω hqt _ ?_ ?_ ?_
  · -- borné
    refine isBounded_iff_forall_norm_le.2 ⟨(C * volume (Ω : Set ℝᵈ) ^ s).toReal, ?_⟩
    rintro f ⟨u, hu, hfu⟩
    rw [Lp.norm_def, eLpNorm_congr_ae hfu]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hs0.le hΩf)) (hloc u hu _ subset_rfl)
  · -- régularité sous translation
    intro K hKc hKΩ
    obtain ⟨A, hA_def⟩ : ∃ A : ℝ≥0∞,
        A = d * volume K ^ (1 / (2⁻¹ : ℝ≥0∞).toReal - 1 / p.toReal) := ⟨_, rfl⟩
    have hA : A ≠ ∞ := by
      rw [hA_def]
      refine ENNReal.mul_ne_top (ENNReal.natCast_ne_top d)
        (ENNReal.rpow_ne_top_of_nonneg ?_ hKc.measure_lt_top.ne)
      have h1 : 1 / p.toReal ≤ 1 := by
        rw [div_le_one (ENNReal.toReal_pos (zero_lt_one.trans hp).ne' hpt), ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hpt hp.le
      have h2 : 1 / (2⁻¹ : ℝ≥0∞).toReal = 2 := by norm_num
      linarith
    have hB : (2 * (C : ℝ≥0∞)) ^ θ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hθ0.le
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top)
    refine ⟨fun t => ((t : ℝ≥0∞) * A) ^ (1 - θ) * (2 * C) ^ θ, ?_, ?_⟩
    · change Tendsto _ (𝓝 0) (𝓝 0)
      have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ≥0∞) * A) (𝓝 0) (𝓝 (((0 : ℝ≥0) : ℝ≥0∞) * A)) :=
        ENNReal.Tendsto.mul_const (ENNReal.continuous_coe.tendsto 0) (Or.inr hA)
      have h2 := ENNReal.Tendsto.mul_const
        (((ENNReal.continuous_rpow_const (y := 1 - θ)).tendsto _).comp h1) (Or.inr hB)
      rwa [ENNReal.coe_zero, zero_mul, ENNReal.zero_rpow_of_pos (by linarith), zero_mul] at h2
    rintro f ⟨u, hu, hfu⟩ h hKh
    have hKh' : ∀ x ∈ K, x - h ∈ (Ω : Set ℝᵈ) := fun x hx =>
      hKh (mem_cthickening_of_dist_le _ x _ _ hx (by rw [dist_eq_norm, sub_sub_cancel_left,
        norm_neg]))
    have hfF : (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)]
        (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) :=
      hfu.trans ((ae_restrict_mem hΩm).mono fun x hx => (indicator_of_mem hx _).symm)
    have hfK : (f : ℝᵈ → ℝ) =ᵐ[volume.restrict K]
        (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) :=
      ae_restrict_of_ae_restrict_of_subset hKΩ hfF
    have hc : (fun x => (f : ℝᵈ → ℝ) x - f (x - h)) =ᵐ[volume.restrict K] fun x =>
        (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) x -
          (Ω : Set ℝᵈ).indicator ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) (x - h) :=
      hfK.sub (rellich_ae_comp_sub hfF hΩm hKc.measurableSet h hKh')
    change _ ≤ ((‖h‖₊ : ℝ≥0∞) * A) ^ (1 - θ) * (2 * C) ^ θ
    rw [eLpNorm_congr_ae hc, hA_def]
    exact rellich_transl hpt hps1 hCu hθ0 hθ1 hpθ hKc hKΩ u hu h hKh
  · -- masse évanescente au bord
    intro ε hε
    have ht : Tendsto (fun x : ℝ≥0∞ => (C : ℝ≥0∞) * x ^ s) (𝓝 0) (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul ((ENNReal.continuous_rpow_const (y := s)).tendsto 0)
        (Or.inr ENNReal.coe_ne_top) (a := (C : ℝ≥0∞))
      rwa [ENNReal.zero_rpow_of_pos hs0, mul_zero] at this
    obtain ⟨η, hη0, hη⟩ :=
      ENNReal.nhds_zero_basis.mem_iff.1 (ht (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε)))
    obtain ⟨K, hKΩ, hKc, hK⟩ := hΩm.exists_isCompact_sdiff_lt hΩf hη0.ne'
    refine ⟨K, hKc, hKΩ, ?_⟩
    rintro f ⟨u, hu, hfu⟩
    rw [eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset sdiff_subset hfu)]
    exact (hloc u hu _ sdiff_subset).trans (hη hK).le

/-- Choix d'un exposant sous-critique `p' ∈ ]1, d[` avec `q < p'*`. -/
private lemma rellich_exists_exponent {q : ℝ≥0∞} (hd : (1 : ℝ≥0∞) < d) (hq1 : 1 ≤ q)
    (hqt : q ≠ ∞) :
    ∃ p' pstar' : ℝ≥0∞, 1 < p' ∧ p' < d ∧ pstar'⁻¹ = p'⁻¹ - (d : ℝ≥0∞)⁻¹ ∧ q < pstar' := by
  have hD : (1 : ℝ) < d := by exact_mod_cast hd
  have hD0 : (0 : ℝ) < d := zero_lt_one.trans hD
  obtain ⟨Q, hQ_def⟩ : ∃ Q : ℝ, Q = q.toReal := ⟨_, rfl⟩
  have hQ : 1 ≤ Q := by rw [hQ_def, ← ENNReal.toReal_one]; exact ENNReal.toReal_mono hqt hq1
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hdinv : 1 / (d : ℝ) < 1 := (div_lt_one hD0).2 hD
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = min (1 / Q) (1 - 1 / (d : ℝ)) := ⟨_, rfl⟩
  have hm0 : 0 < m := hm_def ▸ lt_min (by positivity) (by linarith)
  have hm1 : m ≤ 1 / Q := hm_def ▸ min_le_left _ _
  have hm2 : m ≤ 1 - 1 / (d : ℝ) := hm_def ▸ min_le_right _ _
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = 1 / (d : ℝ) + m / 2 := ⟨_, rfl⟩
  have hd0' : 0 < 1 / (d : ℝ) := by positivity
  have ht0 : 0 < t := by rw [ht_def]; positivity
  have ht1 : t < 1 := by rw [ht_def]; linarith
  have htd : 1 / (d : ℝ) < t := by rw [ht_def]; linarith
  have htq : t - 1 / (d : ℝ) < 1 / Q := by rw [ht_def]; linarith
  have hdE : ((d : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / (d : ℝ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hD0, one_div]
  refine ⟨ENNReal.ofReal (1 / t), ((ENNReal.ofReal (1 / t))⁻¹ - (d : ℝ≥0∞)⁻¹)⁻¹, ?_, ?_,
    by rw [inv_inv], ?_⟩
  · exact ENNReal.one_lt_ofReal.2 (one_lt_one_div ht0 ht1)
  · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_lt_ofReal_iff hD0, div_lt_iff₀ ht0]
    rw [div_lt_iff₀ hD0] at htd
    linarith
  · rw [ENNReal.lt_inv_iff_lt_inv, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div,
      inv_inv, hdE, ← ENNReal.ofReal_sub _ hd0'.le, ← ENNReal.ofReal_toReal hqt,
      ← ENNReal.ofReal_inv_of_pos (hQ_def ▸ hQ0),
      ENNReal.ofReal_lt_ofReal_iff (inv_pos.2 (hQ_def ▸ hQ0)),
      ← hQ_def, ← one_div]
    exact htq

/-- **Point technique (Inclusion `W^{1,p} ⊂ W^{1,p'}`).** Pour `p' ≤ p < ∞` et `Ω` de mesure
finie, l'inclusion `W^{1,p}(Ω) ⊂ W^{1,p'}(Ω)` est continue (Hölder sur `u` et `∇u`). Dans
Lean, `W^{1,p}` et `W^{1,p'}` sont des types distincts, et l'inclusion doit être construite.
Utilisé pour `th:Rellich`. -/
lemma W1p_inclusion_of_le {Ω : TopologicalSpace.Opens ℝᵈ} (hΩf : volume (Ω : Set ℝᵈ) ≠ ∞)
    {p p' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] (hpt : p ≠ ∞) (hpp : p' ≤ p) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : W1p Ω p, ∃ v : W1p Ω p', ‖v‖ ≤ c * ‖u‖ ∧
      ((v : LpGrad Ω p').fst : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)]
        (u : LpGrad Ω p).fst := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) := isFiniteMeasure_restrict.2 hΩf
  have hp'0 : 0 < p'.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p')).ne' (ne_top_of_le_ne_top hpt hpp)
  have hex : 0 ≤ 1 / p'.toReal - 1 / p.toReal :=
    sub_nonneg.2 (one_div_le_one_div_of_le hp'0 (ENNReal.toReal_mono hpt hpp))
  let ι : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) → Lp ℝ p' (volume.restrict (Ω : Set ℝᵈ)) :=
    fun f => ((Lp.memLp f).mono_exponent hpp).toLp f
  have hι : ∀ f, (ι f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] f := fun f =>
    MemLp.coeFn_toLp _
  obtain ⟨V, hV0, hV⟩ : ∃ V : ℝ, 0 ≤ V ∧ ∀ f, ‖ι f‖ ≤ V * ‖f‖ := by
    refine ⟨(volume.restrict (Ω : Set ℝᵈ) univ ^ (1 / p'.toReal - 1 / p.toReal)).toReal,
      ENNReal.toReal_nonneg, fun f => ?_⟩
    rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (hι f), ← ENNReal.toReal_mul, mul_comm]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f)
      (ENNReal.rpow_ne_top_of_nonneg hex (measure_ne_top _ _)))
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpp (Lp.aestronglyMeasurable f))
  set K₁ : ℝ≥0 := (2 : ℝ≥0) ^ (1 / p').toReal
  set K₂ : ℝ≥0 := (Fintype.card (Fin d) : ℝ≥0) ^ (1 / p').toReal
  refine ⟨K₁ * (1 + K₂) * V + 1, by positivity, fun u => ?_⟩
  let w : LpGrad Ω p' := WithLp.toLp p' (ι (u : LpGrad Ω p).fst,
    WithLp.toLp p' fun i => ι ((u : LpGrad Ω p).snd i))
  have hw : w ∈ W1p Ω p' := by
    rw [mem_W1p]
    intro i
    have h1 : Distribution.ofFun Ω (w.fst : ℝᵈ → ℝ) volume ⊤ =
        Distribution.ofFun Ω ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) volume ⊤ :=
      Distribution.ofFun_congr_ae (hι _)
    have h2 : Distribution.ofFun Ω (w.snd i : ℝᵈ → ℝ) volume ⊤ =
        Distribution.ofFun Ω ((u : LpGrad Ω p).snd i : ℝᵈ → ℝ) volume ⊤ :=
      Distribution.ofFun_congr_ae (hι _)
    rw [h1, h2]
    exact mem_W1p.mp u.2 i
  refine ⟨⟨w, hw⟩, ?_, hι _⟩
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hfst : ‖ι (u : LpGrad Ω p).fst‖ ≤ V * ‖u‖ :=
    (hV _).trans (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le _ _) hV0)
  have hsnd : ‖(fun i => ι ((u : LpGrad Ω p).snd i))‖ ≤ V * ‖u‖ := by
    refine pi_norm_le_iff_of_nonneg (by positivity) |>.2 fun i => ?_
    refine (hV _).trans (mul_le_mul_of_nonneg_left ?_ hV0)
    exact (PiLp.norm_apply_le _ i).trans (WithLp.norm_snd_le _ _)
  have hB : ‖WithLp.toLp p' fun i => ι ((u : LpGrad Ω p).snd i)‖ ≤ K₂ * (V * ‖u‖) := by
    have := (PiLp.lipschitzWith_toLp p' (fun _ : Fin d => Lp ℝ p' (volume.restrict
      (Ω : Set ℝᵈ)))).dist_le_mul (fun i => ι ((u : LpGrad Ω p).snd i)) 0
    rw [WithLp.toLp_zero, dist_zero_right, dist_zero_right] at this
    exact this.trans (mul_le_mul_of_nonneg_left hsnd (by positivity))
  have hA := (WithLp.prod_lipschitzWith_toLp p' (Lp ℝ p' (volume.restrict (Ω : Set ℝᵈ)))
    (PiLp p' fun _ : Fin d => Lp ℝ p' (volume.restrict (Ω : Set ℝᵈ)))).dist_le_mul
      (ι (u : LpGrad Ω p).fst, WithLp.toLp p' fun i => ι ((u : LpGrad Ω p).snd i)) 0
  rw [WithLp.toLp_zero, dist_zero_right, dist_zero_right, Prod.norm_def] at hA
  have hK₂ : (0 : ℝ) ≤ K₂ := by positivity
  have hmax : max ‖ι (u : LpGrad Ω p).fst‖ ‖WithLp.toLp p' fun i => ι ((u : LpGrad Ω p).snd i)‖
      ≤ (1 + K₂) * V * ‖u‖ := by
    refine max_le (hfst.trans ?_) (hB.trans ?_) <;> nlinarith [mul_nonneg hV0 hu0]
  calc ‖(⟨w, hw⟩ : W1p Ω p')‖ = ‖w‖ := rfl
    _ ≤ K₁ * ((1 + K₂) * V * ‖u‖) := hA.trans (mul_le_mul_of_nonneg_left hmax (by positivity))
    _ ≤ (K₁ * (1 + K₂) * V + 1) * ‖u‖ := by nlinarith

/-- **Th. `th:Rellich` (Rellich), cas critique** (`p = d > 1`, `q ∈ [1, ∞[`). Mêmes conclusions
que le cas sous-critique. Preuve : celle du cours, via l'injection continue
`W^{1,p}(Ω) ⊂ W^{1,p'}(Ω)` (`Ω` borné) pour un `p' ∈ ]1, d[` tel que `q < p'*`. -/
theorem th_Rellich_critique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hpd : p = d) (hq : q ≠ ∞) :
    (∀ u : Sobolev1 Ω p, MemLp (u.val : ℝᵈ → ℝ) q (volume.restrict (Ω : Set ℝᵈ))) ∧
      TotallyBounded {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω p, ‖u‖ ≤ 1 ∧
        (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val} := by
  have hd : (1 : ℝ≥0∞) < d := hpd ▸ hp
  obtain ⟨p', pstar', hp'1, hp'd, hpstar', hqp'⟩ := rellich_exists_exponent hd Fact.out hq
  have : Fact (1 ≤ p') := ⟨hp'1.le⟩
  have hpt : p ≠ ∞ := hpd ▸ ENNReal.natCast_ne_top d
  obtain ⟨c, hc0, hc⟩ := W1p_inclusion_of_le hΩb.measure_lt_top.ne hpt (hpd ▸ hp'd.le : p' ≤ p)
  obtain ⟨hM, hT⟩ := th_Rellich_sousCritique Ω hΩb hΩ hp'1 hp'd hpstar' hqp'
  simp only [Sobolev1.val_def] at hM hT ⊢
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨v, -, hv⟩ := hc u
    exact (hM v).ae_eq hv
  refine (hT.image (uniformContinuous_const_smul (max c 1))).subset ?_
  rintro f ⟨u, hu, hfu⟩
  obtain ⟨v, hv, hvu⟩ := hc u
  have hc1 : 0 < max c 1 := lt_max_of_lt_right one_pos
  refine ⟨(max c 1)⁻¹ • f, ⟨(max c 1)⁻¹ • v, ?_, ?_⟩, smul_inv_smul₀ hc1.ne' f⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc1.le), inv_mul_le_iff₀ hc1, mul_one]
    calc ‖v‖ ≤ c * ‖u‖ := hv
      _ ≤ max c 1 * 1 := mul_le_mul (le_max_left _ _) hu (norm_nonneg _) hc1.le
      _ = max c 1 := mul_one _
  · have e : (((max c 1)⁻¹ • v : W1p Ω p') : LpGrad Ω p').fst =
        (max c 1)⁻¹ • (v : LpGrad Ω p').fst := rfl
    rw [e]
    filter_upwards [Lp.coeFn_smul (max c 1)⁻¹ f, Lp.coeFn_smul (max c 1)⁻¹
      (v : LpGrad Ω p').fst, hfu, hvu] with x h1 h2 h3 h4
    rw [h1, h2, Pi.smul_apply, Pi.smul_apply, h3, h4]

/-! ### Cas sur-critique -/

/-- Une famille uniformément höldérienne est uniformément équicontinue. -/
private lemma rellich_uniformEquicont {ι X : Type*} [PseudoMetricSpace X] {F : ι → X → ℝ}
    {K α : ℝ} (hα : 0 < α) (hF : ∀ i x y, |F i x - F i y| ≤ K * dist x y ^ α) :
    UniformEquicontinuous F := by
  refine Metric.uniformEquicontinuous_of_continuity_modulus (fun t => K * t ^ α) ?_ F
    fun x y i => by rw [Real.dist_eq]; exact hF i x y
  have := ((Real.continuous_rpow_const hα.le).tendsto 0).const_mul K
  rwa [Real.zero_rpow hα.ne', mul_zero] at this

private lemma rellich_isUniformInducing_incl {X : Type*} [MetricSpace X] (U : Set X) :
    IsUniformInducing (Set.inclusion (subset_closure : U ⊆ closure U)) :=
  (isUniformInducing_val (closure U)).of_comp_iff.1 (isUniformInducing_val U)

private lemma rellich_denseRange_incl {X : Type*} [MetricSpace X] (U : Set X) :
    DenseRange (Set.inclusion (subset_closure : U ⊆ closure U)) :=
  (denseRange_inclusion_iff _).2 subset_rfl

/-- Prolongement à `closure U` d'une fonction höldérienne sur `U`. -/
private lemma rellich_extend {X : Type*} [MetricSpace X] {U : Set X} {v : X → ℝ} {K α : ℝ}
    (hα : 0 < α) (hv : ∀ x ∈ U, ∀ y ∈ U, |v x - v y| ≤ K * dist x y ^ α) :
    ∃ g : C(closure U, ℝ), ∀ x (hx : x ∈ U), g ⟨x, subset_closure hx⟩ = v x := by
  have hf : UniformContinuous fun x : U => v x :=
    (rellich_uniformEquicont (ι := Unit) (F := fun _ (x : U) => v x) hα
      fun _ x y => hv x x.2 y y.2).uniformContinuous ()
  have he := rellich_isUniformInducing_incl U
  have hd := rellich_denseRange_incl U
  exact ⟨⟨_, (uniformContinuous_uniformly_extend he hd hf).continuous⟩,
    fun x hx => uniformly_extend_of_ind he hd hf ⟨x, hx⟩⟩

/-- Les estimations de borne et de Hölder passent de `U` à `closure U`. -/
private lemma rellich_closure_le {X : Type*} [MetricSpace X] {U : Set X} (g : C(closure U, ℝ))
    {C K α : ℝ} (hα : 0 < α) (hb : ∀ x (hx : x ∈ U), |g ⟨x, subset_closure hx⟩| ≤ C)
    (hh : ∀ x (hx : x ∈ U) y (hy : y ∈ U),
      |g ⟨x, subset_closure hx⟩ - g ⟨y, subset_closure hy⟩| ≤ K * dist x y ^ α) :
    (∀ x, |g x| ≤ C) ∧ ∀ x y, |g x - g y| ≤ K * dist x y ^ α := by
  have hd := rellich_denseRange_incl U
  refine ⟨fun x => hd.induction_on x (isClosed_le (continuous_abs.comp g.continuous)
    continuous_const) fun a => hb a a.2, fun x y => ?_⟩
  refine hd.induction_on₂ (p := fun x y => |g x - g y| ≤ K * dist x y ^ α) ?_
    (fun a b => hh a a.2 b b.2) x y
  exact isClosed_le (continuous_abs.comp ((g.continuous.comp continuous_fst).sub
    (g.continuous.comp continuous_snd))) (continuous_const.mul
      ((Real.continuous_rpow_const hα.le).comp continuous_dist))

/-- En dimension `0`, `|u(x)| ≤ ‖u‖` en tout point `x ∈ Ω`. -/
private lemma rellich_rep_zero {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 0))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : W1p Ω p) {x : EuclideanSpace ℝ (Fin 0)}
    (hx : x ∈ (Ω : Set (EuclideanSpace ℝ (Fin 0)))) :
    |((u : LpGrad Ω p).fst : EuclideanSpace ℝ (Fin 0) → ℝ) x| ≤ ‖u‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hΩ : (Ω : Set (EuclideanSpace ℝ (Fin 0))) = univ :=
    eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
  have hvol : volume (univ : Set (EuclideanSpace ℝ (Fin 0))) = 1 := by
    have := (PiLp.volume_preserving_toLp (ι := Fin 0)).measure_preimage
      (s := (univ : Set (EuclideanSpace ℝ (Fin 0)))) nullMeasurableSet_univ
    rw [preimage_univ] at this
    rw [← this, volume_pi, Measure.pi_univ]; simp
  set c := ((u : LpGrad Ω p).fst : EuclideanSpace ℝ (Fin 0) → ℝ) x
  have hc : ((u : LpGrad Ω p).fst : EuclideanSpace ℝ (Fin 0) → ℝ) = fun _ => c :=
    funext fun y => by rw [Subsingleton.elim y x]
  have hμ : volume.restrict (Ω : Set (EuclideanSpace ℝ (Fin 0))) ≠ 0 := by
    rw [hΩ, Measure.restrict_univ]; intro h; simp [h] at hvol
  have hn : ‖(u : LpGrad Ω p).fst‖ = |c| := by
    rw [Lp.norm_def, hc, eLpNorm_const c hp0 hμ, Measure.restrict_apply_univ, hΩ, hvol,
      ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [← hn]
  exact WithLp.norm_fst_le _ _

/-- Représentant continu et estimations (`corol_injSurCritOm`, et cas trivial `d = 0`). -/
private lemma rellich_surCrit_rep (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞) (hP : ProlongementSobolev Ω p) :
    ∃ C C' : ℝ, ∀ u : W1p Ω p, ∃ v : ℝᵈ → ℝ, ContinuousOn v Ω ∧
      ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v ∧
      (∀ x ∈ (Ω : Set ℝᵈ), |v x| ≤ C * ‖u‖) ∧
      (∀ x ∈ (Ω : Set ℝᵈ), ∀ y ∈ (Ω : Set ℝᵈ),
        |v x - v y| ≤ C' * dist x y ^ (1 - d / p.toReal) * ‖u‖) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨1, 0, fun u => ⟨fun _ => ((u : LpGrad Ω p).fst : EuclideanSpace ℝ (Fin 0) → ℝ) 0,
      continuousOn_const, Eventually.of_forall fun y => by rw [Subsingleton.elim y 0],
      fun x hx => ?_, fun x _ y _ => by simp⟩⟩
    rw [one_mul, Subsingleton.elim (0 : EuclideanSpace ℝ (Fin 0)) x]
    exact rellich_rep_zero u hx
  · exact corol_injSurCritOm Ω hd hdp hp hP

/-- **Point technique (Représentant höldérien sur l'adhérence).** Si `f` admet sur `Ω` un
représentant continu `v`, borné par `C` et `α`-höldérien de constante `K`, alors tout
représentant `g ∈ C(adh Ω)` de `f` vérifie les mêmes estimations sur `adh Ω`. Le cours passe
sous silence le choix du représentant continu, et son prolongement à l'adhérence. Utilisé
pour `th:Rellich`. -/
lemma holder_representant_adherence {Ω : TopologicalSpace.Opens ℝᵈ} {f v : ℝᵈ → ℝ} {C K α : ℝ}
    (hα : 0 < α) (g : C(closure (Ω : Set ℝᵈ), ℝ))
    (hgu : ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
      f x = g ⟨x, hx⟩)
    (hvc : ContinuousOn v Ω) (hvae : f =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v)
    (hvb : ∀ x ∈ (Ω : Set ℝᵈ), |v x| ≤ C)
    (hvh : ∀ x ∈ (Ω : Set ℝᵈ), ∀ y ∈ (Ω : Set ℝᵈ), |v x - v y| ≤ K * dist x y ^ α) :
    (∀ x, |g x| ≤ C) ∧ ∀ x y, |g x - g y| ≤ K * dist x y ^ α := by
  classical
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  let G : ℝᵈ → ℝ := fun x => if hx : x ∈ closure (Ω : Set ℝᵈ) then g ⟨x, hx⟩ else 0
  have hG : ∀ x (hx : x ∈ closure (Ω : Set ℝᵈ)), G x = g ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hGc : ContinuousOn G (Ω : Set ℝᵈ) := by
    refine ContinuousOn.mono ?_ (subset_closure : (Ω : Set ℝᵈ) ⊆ closure (Ω : Set ℝᵈ))
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (closure (Ω : Set ℝᵈ)).domRestrict G = g := funext fun x => hG x x.2
    rw [e]; exact g.continuous
  have hGv : G =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v := by
    filter_upwards [hgu, hvae, ae_restrict_mem hΩm] with x h1 h2 h3
    rw [← h2, h1 (subset_closure h3), hG]
  have heq := Measure.eqOn_open_of_ae_eq hGv Ω.isOpen hGc hvc
  have hgv : ∀ x (hx : x ∈ (Ω : Set ℝᵈ)), g ⟨x, subset_closure hx⟩ = v x := fun x hx => by
    rw [← heq hx, hG]
  refine rellich_closure_le g hα (fun x hx => ?_) (fun x hx y hy => ?_)
  · rw [hgv x hx]; exact hvb x hx
  · rw [hgv x hx, hgv y hy]; exact hvh x hx y hy

/-- Arzelà–Ascoli : les fonctions bornées par `C` et `α`-höldériennes de constante `K` forment
une partie précompacte de `C(X, ℝ)`, `X` compact. -/
private lemma rellich_totallyBounded_holder {X : Type*} [MetricSpace X] [CompactSpace X]
    {C K α : ℝ} (hα : 0 < α) :
    TotallyBounded {g : C(X, ℝ) | (∀ x, |g x| ≤ C) ∧ ∀ x y, |g x - g y| ≤ K * dist x y ^ α} := by
  let Φ := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  let B := {g : C(X, ℝ) | (∀ x, |g x| ≤ C) ∧ ∀ x y, |g x - g y| ≤ K * dist x y ^ α}
  have hA : TotallyBounded (Φ '' B) := by
    refine (BoundedContinuousFunction.arzela_ascoli (Icc (-C) C) isCompact_Icc (Φ '' B)
      ?_ ?_).totallyBounded.subset subset_closure
    · rintro f x ⟨g, hg, rfl⟩
      exact abs_le.1 (hg.1 x)
    · refine (rellich_uniformEquicont (K := K) hα fun f x y => ?_).equicontinuous
      obtain ⟨g, hg, hgf⟩ := f.2
      rw [← hgf]
      exact hg.2 x y
  have := hA.image Φ.symm.isometry.uniformContinuous
  rwa [← Set.image_comp, show ⇑Φ.symm ∘ ⇑Φ = id from funext Φ.symm_apply_apply,
    Set.image_id] at this

/-- **Th. `th:Rellich` (Rellich), cas sur-critique** (`d < p < ∞`). Tout `u ∈ W^{1,p}(Ω)` a un
représentant continu sur `Ω̄`, et la boule unité fermée de `W^{1,p}(Ω)` est précompacte dans
`C(Ω̄)`. Preuve : celle du cours (bornes de Morrey `corol_injSurCritOm`, prolongement
uniformément continu à `Ω̄`, Arzelà–Ascoli de Mathlib). -/
theorem th_Rellich_surCritique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞) :
    (∀ u : Sobolev1 Ω p, ∃ g : C(closure (Ω : Set ℝᵈ), ℝ),
      ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
        u.val x = g ⟨x, hx⟩) ∧
      TotallyBounded {g : C(closure (Ω : Set ℝᵈ), ℝ) | ∃ u : Sobolev1 Ω p, ‖u‖ ≤ 1 ∧
        ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
          u.val x = g ⟨x, hx⟩} := by
  simp only [Sobolev1.val_def]
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  have hP0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hdpr : (d : ℝ) < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (ENNReal.natCast_ne_top d) hp).2 hdp
    simpa using this
  obtain ⟨α, hα_def⟩ : ∃ α : ℝ, α = 1 - d / p.toReal := ⟨_, rfl⟩
  have hα : 0 < α := by rw [hα_def, sub_pos, div_lt_one hP0]; exact hdpr
  obtain ⟨C, C', hCC⟩ := rellich_surCrit_rep Ω hdp hp (hΩ p)
  simp_rw [← hα_def] at hCC
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨v, -, hvae, -, hvh⟩ := hCC u
    obtain ⟨g, hg⟩ := rellich_extend (K := C' * ‖u‖) hα fun x hx y hy => by
      rw [mul_right_comm]; exact hvh x hx y hy
    refine ⟨g, ?_⟩
    filter_upwards [hvae, ae_restrict_mem hΩm] with x h1 h2
    intro hx
    rw [h1]
    exact (hg x h2).symm
  have : CompactSpace (closure (Ω : Set ℝᵈ)) :=
    isCompact_iff_compactSpace.1 hΩb.isCompact_closure
  refine TotallyBounded.subset ?_ (rellich_totallyBounded_holder (C := max C 0)
    (K := max C' 0) hα)
  rintro g ⟨u, hu, hgu⟩
  obtain ⟨v, hvc, hvae, hvb, hvh⟩ := hCC u
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  refine holder_representant_adherence hα g hgu hvc hvae (fun x hx => (hvb x hx).trans ?_)
    (fun x hx y hy => (hvh x hx y hy).trans ?_)
  · nlinarith [le_max_left C 0, le_max_right C 0]
  · have hd0 : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 (le_max_left C' 0)) hd0) hu0,
      mul_nonneg (mul_nonneg (le_max_right C' 0) hd0) (sub_nonneg.2 hu)]

end RellichW1p

end M1Analyse
