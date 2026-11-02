/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Dualite.Reflexivite
import Mathlib.Analysis.Convex.Uniform
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# §3.2 Réflexivité : dualité dans les espaces de Lebesgue (`subsec:reflexivite`, fin)

Source : `Include/Dualite.tex`, fin de la sous-section `subsec:reflexivite` (paragraphe
« Dualité dans les espaces de Lebesgue »).

Les espaces `L^p` sont ceux de Mathlib (`Lp ℝ p μ`, `eLpNorm`), les espaces de suites `ℓ^p`
sont `lp (fun _ : ℕ => ℝ) p`, et `ℓ^∞_0` (suites tendant vers `0`) est `C₀(ℕ, ℝ)`.
L'application `g ↦ φ_g` est `dualLp` (construite à partir de `lpPairing` de Mathlib).

La bijectivité de `th:lpDualLq` repose sur le théorème de Milman–Pettis, posé comme **axiome**
(`th_unifCvxReflex`, voir `Reflexivite.lean`). Pour `p = 1`, l'isométrie suppose `μ` `σ`-finie
(l'énoncé du cours est faux sans hypothèse sur `μ`) ; la bijectivité pour `p = 1`
(`th_lpDualLq_bijectif_un`, non démontrée dans le cours) est prouvée sans Milman–Pettis, via
le théorème de Riesz dans `L^2` pour un poids `u > 0` de carré intégrable.
-/

open NormedSpace MeasureTheory Filter Topology
open scoped ENNReal ZeroAtInfty

namespace M1Analyse

section Lebesgue
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}


/-- Inégalité ponctuelle de Clarkson (réelle), pour `2 ≤ p`. -/
private lemma clarkson_real {p : ℝ} (hp : 2 ≤ p) (a b : ℝ) :
    |(a + b) / 2| ^ p + |(a - b) / 2| ^ p ≤ |a| ^ p / 2 + |b| ^ p / 2 := by
  set s := p / 2 with hs
  have hs1 : 1 ≤ s := by rw [hs]; linarith
  have hsq : ∀ t : ℝ, |t| ^ p = (t ^ 2) ^ s := fun t => by
    rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg t), hs]
    congr 1; ring
  rw [hsq, hsq, hsq a, hsq b]
  calc (((a + b) / 2) ^ 2) ^ s + (((a - b) / 2) ^ 2) ^ s
      ≤ (((a + b) / 2) ^ 2 + ((a - b) / 2) ^ 2) ^ s := by
        have := NNReal.add_rpow_le_rpow_add ⟨_, sq_nonneg ((a + b) / 2)⟩
          ⟨_, sq_nonneg ((a - b) / 2)⟩ hs1
        exact_mod_cast this
    _ = ((1 / 2 : ℝ) • a ^ 2 + (1 / 2 : ℝ) • b ^ 2) ^ s := by
        congr 1; simp only [smul_eq_mul]; ring
    _ ≤ (1 / 2 : ℝ) • (a ^ 2) ^ s + (1 / 2 : ℝ) • (b ^ 2) ^ s :=
        (convexOn_rpow hs1).2 (Set.mem_Ici.2 (sq_nonneg a)) (Set.mem_Ici.2 (sq_nonneg b))
          (by norm_num) (by norm_num) (by norm_num)
    _ = (a ^ 2) ^ s / 2 + (b ^ 2) ^ s / 2 := by simp only [smul_eq_mul]; ring

/-- Version `ℝ≥0∞` de l'inégalité ponctuelle. -/
private lemma clarkson_enorm {p : ℝ} (hp : 2 ≤ p) (a b : ℝ) :
    ‖(a + b) / 2‖ₑ ^ p + ‖(a - b) / 2‖ₑ ^ p ≤ ‖a‖ₑ ^ p / 2 + ‖b‖ₑ ^ p / 2 := by
  have h0 : 0 ≤ p := by linarith
  simp only [Real.enorm_eq_ofReal_abs]
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) h0,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) h0,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) h0,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) h0,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hd : ∀ x : ℝ, ENNReal.ofReal x / 2 = ENNReal.ofReal (x / 2) := fun x => by
    rw [ENNReal.ofReal_div_of_pos two_pos, ENNReal.ofReal_ofNat]
  rw [hd, hd, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (clarkson_real hp a b)

/-- **Prop. `prop:ClarksonIneq` (Première inégalité de Clarkson).**
« Soient $2 \leq p < \infty$ et
$f,g\in L^p(X,\mu)$. Alors
$\|\frac{f+g}2\|_p^p + \|\frac{f-g}2\|_p^p \leq \frac12 \|f\|_p^p + \frac12 \|g\|_p^p$. » -/
theorem prop_ClarksonIneq {p : ℝ≥0∞} (hp : 2 ≤ p) (hp' : p ≠ ∞) {f g : X → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g p μ) :
    eLpNorm (fun x => (f x + g x) / 2) p μ ^ p.toReal +
        eLpNorm (fun x => (f x - g x) / 2) p μ ^ p.toReal ≤
      eLpNorm f p μ ^ p.toReal / 2 + eLpNorm g p μ ^ p.toReal / 2 := by
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hp; exact absurd hp (by norm_num)
  have hpr : 2 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp; simpa using this
  have hpos : 0 < p.toReal := by linarith
  have hE : ∀ h : X → ℝ, AEStronglyMeasurable h μ →
      eLpNorm h p μ ^ p.toReal = ∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ := fun h hh => by
    rw [eLpNorm_eq_eLpNorm' hp0 hp' hh, lintegral_rpow_enorm_eq_rpow_eLpNorm' hpos]
  have mf := hf.aestronglyMeasurable
  have mg := hg.aestronglyMeasurable
  have m1 : AEStronglyMeasurable (fun x => (f x + g x) / 2) μ := by fun_prop
  have m2 : AEStronglyMeasurable (fun x => (f x - g x) / 2) μ := by fun_prop
  rw [hE _ m1, hE _ m2, hE _ mf, hE _ mg]
  have hmeas : ∀ h : X → ℝ, MemLp h p μ →
      AEMeasurable (fun x => ‖h x‖ₑ ^ p.toReal * 2⁻¹) μ := fun h hh =>
    (hh.aestronglyMeasurable.enorm.pow_const _).mul_const _
  calc (∫⁻ x, ‖(f x + g x) / 2‖ₑ ^ p.toReal ∂μ) + ∫⁻ x, ‖(f x - g x) / 2‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, (‖(f x + g x) / 2‖ₑ ^ p.toReal + ‖(f x - g x) / 2‖ₑ ^ p.toReal) ∂μ :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ x, (‖f x‖ₑ ^ p.toReal * 2⁻¹ + ‖g x‖ₑ ^ p.toReal * 2⁻¹) ∂μ := by
        refine lintegral_mono fun x => ?_
        have := clarkson_enorm hpr (f x) (g x)
        simpa only [div_eq_mul_inv] using this
    _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) / 2 + (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) / 2 := by
        rw [lintegral_add_left' (hmeas f hf), lintegral_mul_const' _ _ (by simp),
          lintegral_mul_const' _ _ (by simp), div_eq_mul_inv, div_eq_mul_inv]

/-- Version `Lp` réelle de la première inégalité de Clarkson. -/
private lemma clarkson_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞)
    (f g : Lp ℝ p μ) :
    ‖(1 / 2 : ℝ) • (f + g)‖ ^ p.toReal + ‖(1 / 2 : ℝ) • (f - g)‖ ^ p.toReal ≤
      ‖f‖ ^ p.toReal / 2 + ‖g‖ ^ p.toReal / 2 := by
  have H := prop_ClarksonIneq hp hp' (Lp.memLp f) (Lp.memLp g) (μ := μ)
  have e1 : eLpNorm (fun x => (f x + g x) / 2) p μ =
      eLpNorm (⇑((1 / 2 : ℝ) • (f + g))) p μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f + g), Lp.coeFn_add f g] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.add_apply, smul_eq_mul]; ring
  have e2 : eLpNorm (fun x => (f x - g x) / 2) p μ =
      eLpNorm (⇑((1 / 2 : ℝ) • (f - g))) p μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (f - g), Lp.coeFn_sub f g] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, smul_eq_mul]; ring
  rw [e1, e2] at H
  have hpos : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have fin : ∀ u : Lp ℝ p μ, eLpNorm u p μ ^ p.toReal ≠ ∞ := fun u =>
    ENNReal.rpow_ne_top_of_nonneg hpos (Lp.eLpNorm_ne_top u)
  have := ENNReal.toReal_mono
    (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (fin f) (by norm_num),
      ENNReal.div_ne_top (fin g) (by norm_num)⟩) H
  rw [ENNReal.toReal_add (fin _) (fin _),
    ENNReal.toReal_add (ENNReal.div_ne_top (fin f) (by norm_num))
      (ENNReal.div_ne_top (fin g) (by norm_num)),
    ENNReal.toReal_div, ENNReal.toReal_div] at this
  simpa only [Lp.norm_def, ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] using this

/-- Uniforme convexité de $L^p$, $2 \leq p < \infty$, conséquence de la première inégalité de
Clarkson (`prop:ClarksonIneq`) : si $\|f\|_p=\|g\|_p=1$ et $\|f-g\|_p \geq \varepsilon$, alors
$\|\frac{f+g}2\|_p^p \leq 1-(\varepsilon/2)^p$. -/
theorem prop_ClarksonIneq_unifCvx {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    UniformConvexSpace (Lp ℝ p μ) := by
  have hpr : 2 ≤ p.toReal := by
    have := ENNReal.toReal_mono hp' hp; simpa using this
  have hpos : 0 < p.toReal := by linarith
  refine unifCvx_iff_uniformConvexSpace.1 fun ε hε => ?_
  set η := (min ε 1 / 2) ^ p.toReal with hη
  have hm0 : 0 < min ε 1 / 2 := by positivity
  have hm1 : min ε 1 / 2 < 1 := by
    have := min_le_right ε 1; linarith
  have hη0 : 0 < η := Real.rpow_pos_of_pos hm0 _
  have hη1 : η < 1 := Real.rpow_lt_one hm0.le hm1 hpos
  refine ⟨1 - (1 - η) ^ (1 / p.toReal), ?_, fun f g hf hg hfg => ?_⟩
  · have := Real.rpow_lt_one (by linarith : (0 : ℝ) ≤ 1 - η) (by linarith) (by positivity :
      (0 : ℝ) < 1 / p.toReal)
    linarith
  · have H := clarkson_Lp hp hp' f g (μ := μ)
    rw [hf, hg, Real.one_rpow] at H
    have hd : min ε 1 / 2 ≤ ‖(1 / 2 : ℝ) • (f - g)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := min_le_left ε 1; linarith
    have hd' : η ≤ ‖(1 / 2 : ℝ) • (f - g)‖ ^ p.toReal :=
      Real.rpow_le_rpow hm0.le hd hpos.le
    have ht : ‖(1 / 2 : ℝ) • (f + g)‖ ^ p.toReal ≤ 1 - η := by linarith
    have := Real.rpow_le_rpow (by positivity) ht (by positivity : (0 : ℝ) ≤ 1 / p.toReal)
    rw [← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hpos.ne', Real.rpow_one] at this
    linarith


/-- Les trois cas possibles pour un couple d'exposants conjugués. -/
private lemma dualLp_conj_cases {p q : ℝ≥0∞} [Fact (1 ≤ p)] [q.HolderConjugate p] :
    (p = 1 ∧ q = ∞) ∨ (p = ∞ ∧ q = 1) ∨ (1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞) := by
  have h : q⁻¹ + p⁻¹ = 1 := by
    simpa using (‹q.HolderConjugate p› : ENNReal.HolderTriple q p 1).inv_add_inv_eq_inv
  rcases eq_or_lt_of_le (Fact.out : 1 ≤ p) with h1 | h1
  · subst h1
    left
    refine ⟨rfl, ?_⟩
    have : q⁻¹ = 0 := by
      rw [inv_one] at h
      exact (ENNReal.add_left_inj ENNReal.one_ne_top).1 (by rw [h, zero_add])
    simpa using this
  rcases eq_or_lt_of_le (le_top : p ≤ ∞) with h2 | h2
  · subst h2
    right; left
    refine ⟨rfl, ?_⟩
    simpa using h
  right; right
  have hpi0 : p⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h2.ne
  have hpi1 : p⁻¹ < 1 := ENNReal.inv_lt_one.2 h1
  have hqi : q⁻¹ ≠ ∞ := by
    intro hq; rw [hq, top_add] at h; exact ENNReal.top_ne_one h
  refine ⟨h1, h2, ?_, ?_⟩
  · apply ENNReal.inv_lt_one.1
    calc q⁻¹ < q⁻¹ + p⁻¹ := ENNReal.lt_add_right hqi hpi0
      _ = 1 := h
  · refine lt_top_iff_ne_top.2 (ENNReal.inv_pos.1 ?_)
    rw [pos_iff_ne_zero]
    intro hq0
    rw [hq0, zero_add] at h
    exact hpi1.ne h

private lemma dualLp_measurable_sign : Measurable Real.sign := by
  change Measurable fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

private lemma dualLp_sign_mul (r : ℝ) : Real.sign r * r = |r| := by
  rcases lt_trichotomy r 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h, Real.sign_zero]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

private lemma dualLp_abs_sign_le (r : ℝ) : |Real.sign r| ≤ 1 := by
  rcases Real.sign_apply_eq r with h | h | h <;> rw [h] <;> norm_num

/-- Inégalité de Hölder sous la forme `|∫ f g| ≤ ‖f‖_p ‖g‖_q`. -/
private lemma dualLp_norm_integral_le {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (f : Lp ℝ p μ)
    (g : Lp ℝ q μ) : ‖∫ x, f x * g x ∂μ‖ ≤ ‖f‖ * ‖g‖ := by
  calc ‖∫ x, f x * g x ∂μ‖ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂μ := by simp_rw [norm_mul]
    _ ≤ (eLpNorm (fun x => ‖f x‖) p μ).toReal * (eLpNorm (fun x => ‖g x‖) q μ).toReal :=
      (th_HolderIneq hpq (Lp.memLp f).norm (Lp.memLp g).norm).2
    _ = ‖f‖ * ‖g‖ := by
      rw [eLpNorm_norm _ (Lp.aestronglyMeasurable f), eLpNorm_norm _ (Lp.aestronglyMeasurable g),
        Lp.norm_def, Lp.norm_def]

/-- **Point technique (Cas d'égalité de Hölder).** Pour `h ∈ L^r` non nulle (`1 < r < ∞`), la
fonction `k = sign(h) |h|^{r/s}` est dans `L^s`, non nulle, et réalise l'égalité
`∫ k h = ‖k‖_s ‖h‖_r`. Le cours invoque ce cas d'égalité sans le détailler. Utilisé pour
`th:lpDualLq`. -/
lemma holder_cas_egalite {r s : ℝ≥0∞} (hrs : s⁻¹ + r⁻¹ = 1) (hs : 1 < s) (hs' : s < ∞)
    (hr : 1 < r) (hr' : r < ∞) {h : X → ℝ} (hh : MemLp h r μ) (h0 : eLpNorm h r μ ≠ 0) :
    ∃ k : X → ℝ, MemLp k s μ ∧ eLpNorm k s μ ≠ 0 ∧
      ∫ x, k x * h x ∂μ = (eLpNorm k s μ).toReal * (eLpNorm h r μ).toReal := by
  set k : X → ℝ := fun x => Real.sign (h x) * |h x| ^ (r.toReal / s.toReal) with hkdef
  have hr0 : r ≠ 0 := (zero_lt_one.trans hr).ne'
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs).ne'
  have hR : 0 < r.toReal := ENNReal.toReal_pos hr0 hr'.ne
  have hS : 0 < s.toReal := ENNReal.toReal_pos hs0 hs'.ne
  have hkm : AEStronglyMeasurable k μ :=
    ((dualLp_measurable_sign.comp_aemeasurable hh.aestronglyMeasurable.aemeasurable).mul
      ((continuous_abs.measurable.comp_aemeasurable
        hh.aestronglyMeasurable.aemeasurable).pow_const _)).aestronglyMeasurable
  have hkpow : ∀ x, ‖k x‖ ^ s.toReal = ‖h x‖ ^ r.toReal := by
    intro x
    simp only [hkdef, Real.norm_eq_abs, abs_mul]
    rcases eq_or_ne (h x) 0 with hx | hx
    · rw [hx, Real.sign_zero, abs_zero, zero_mul, Real.zero_rpow hS.ne',
        Real.zero_rpow hR.ne']
    · have : |Real.sign (h x)| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero _ hx with h' | h' <;> rw [h'] <;> simp
      rw [this, one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
        ← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ hS.ne']
  have hk : MemLp k s μ := by
    refine (integrable_norm_rpow_iff hkm hs0 hs'.ne).1 ?_
    simp_rw [hkpow]
    exact (integrable_norm_rpow_iff hh.aestronglyMeasurable hr0 hr'.ne).2 hh
  have hk0 : eLpNorm k s μ ≠ 0 := by
    intro hk0
    rw [eLpNorm_eq_zero_iff hs0] at hk0
    apply h0
    rw [eLpNorm_eq_zero_iff hr0]
    filter_upwards [hk0] with x hx
    have := hkpow x
    rw [hx, Pi.zero_apply, norm_zero, Real.zero_rpow hS.ne'] at this
    have h2 := (Real.rpow_eq_zero_iff_of_nonneg (norm_nonneg (h x))).1 this.symm
    exact norm_eq_zero.1 h2.1
  refine ⟨k, hk, hk0, ?_⟩
  have hne : (eLpNorm k s μ).toReal * (eLpNorm h r μ).toReal ≠ 0 :=
    mul_ne_zero (ENNReal.toReal_ne_zero.2 ⟨hk0, hk.eLpNorm_ne_top⟩)
      (ENNReal.toReal_ne_zero.2 ⟨h0, hh.eLpNorm_ne_top⟩)
  exact (th_HolderIneq_eq hrs hs hs' hk hh hne).2 ⟨1, one_pos, ae_of_all _ fun x => by
    simp [hkdef]⟩

/-- Version dans les espaces `L^p` du lemme précédent. -/
private lemma dualLp_exists_eq_Lp {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)] (hrs : s⁻¹ + r⁻¹ = 1)
    (hs : 1 < s) (hs' : s < ∞) (hr : 1 < r) (hr' : r < ∞) (f : Lp ℝ r μ) (hf : f ≠ 0) :
    ∃ k : Lp ℝ s μ, k ≠ 0 ∧ ∫ x, k x * f x ∂μ = ‖k‖ * ‖f‖ := by
  have h0 : eLpNorm f r μ ≠ 0 := by
    have := norm_ne_zero_iff.2 hf
    rw [Lp.norm_def] at this
    exact (ENNReal.toReal_ne_zero.1 this).1
  obtain ⟨k, hk, hk0, hkf⟩ := holder_cas_egalite hrs hs hs' hr hr' (Lp.memLp f) h0
  refine ⟨hk.toLp k, ?_, ?_⟩
  · rw [← norm_ne_zero_iff, Lp.norm_toLp]
    exact ENNReal.toReal_ne_zero.2 ⟨hk0, hk.eLpNorm_ne_top⟩
  · rw [Lp.norm_toLp, Lp.norm_def, ← hkf]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hk] with x hx
    rw [hx]

variable (μ) in
/-- **Th. `th:lpDualLq`, application `g ↦ φ_g`.** Pour `p, q ∈ [1, ∞]` conjugués
(`1/p + 1/q = 1`), `dualLp μ p q : L^q(X,μ) → L^p(X,μ)^*` associe à `g` la forme
`φ_g(f) := ∫_X f g` (`dualLp_apply`). Construite à partir de `lpPairing` de Mathlib (crochet
`∫ B (g x) (f x)` avec `B` la multiplication).
Remarque : `[Fact (1 ≤ p)]` est l'hypothèse `p ≥ 1` passée comme instance ; Mathlib en a besoin
pour munir `Lp ℝ p μ` de sa norme. `[q.HolderConjugate p]` exprime `1/p + 1/q = 1`. -/
noncomputable def dualLp (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p] :
    Lp ℝ q μ →L[ℝ] StrongDual ℝ (Lp ℝ p μ) :=
  (ContinuousLinearMap.mul ℝ ℝ).flip.lpPairing μ q p

/-- **Th. `th:lpDualLq`, définition de `φ_g`.** Pour `g ∈ L^q` et `f ∈ L^p`,
`φ_g(f) = ∫_X f g`. -/
theorem dualLp_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (g : Lp ℝ q μ) (f : Lp ℝ p μ) : dualLp μ p q g f = ∫ x, f x * g x ∂μ := by
  simp [dualLp, ContinuousLinearMap.lpPairing_eq_integral, mul_comm]

/-- **Th. `th:lpDualLq` (Dualité dans les espaces de Lebesgue), isométrie.** Soient
`1 ≤ p ≤ ∞` et `q` l'exposant conjugué. L'application `g ∈ L^q ↦ φ_g ∈ (L^p)^*` est une
injection isométrique : `‖φ_g‖ ≤ ‖g‖_q` par Hölder, et l'égalité s'obtient en testant `φ_g`
sur `sign(g) |g|^{q-1}` (`1 < p < ∞`), sur `sign(g)` (`p = ∞`), ou sur `1_T sign(g)` avec
`T ⊆ {|g| > c}` de mesure finie non nulle (`p = 1`).
Pour `p = 1` on suppose `μ` `σ`-finie : l'énoncé du cours est faux sinon (`X = {*}`,
`μ{*} = ∞` : `L^1 = {0}` et `L^∞ = ℝ`). -/
theorem th_lpDualLq_isometrie {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hμ : p = 1 → SigmaFinite μ) : Isometry (dualLp μ p q) := by
  have hqp : q⁻¹ + p⁻¹ = 1 := by
    simpa using (‹q.HolderConjugate p› : ENNReal.HolderTriple q p 1).inv_add_inv_eq_inv
  have hpq : p⁻¹ + q⁻¹ = 1 := by rw [add_comm]; exact hqp
  refine AddMonoidHomClass.isometry_of_norm _ fun g => le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    rw [dualLp_apply, mul_comm ‖g‖]
    exact dualLp_norm_integral_le hpq f g
  rcases dualLp_conj_cases (p := p) (q := q) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hp1, hp2, hq1, hq2⟩
  · -- `p = 1`, `q = ∞` : on teste sur `1_T sign(g)`, `T ⊆ {|g| > c'}` de mesure finie > 0.
    have := hμ rfl
    by_contra hlt
    push Not at hlt
    set c := ‖dualLp μ 1 ∞ g‖ with hc
    set c' := (c + ‖g‖) / 2 with hc'
    have hcc' : c < c' := by rw [hc']; linarith
    have hc'g : c' < ‖g‖ := by rw [hc']; linarith
    have hc0 : 0 ≤ c := norm_nonneg _
    set S := {x | c' < |g x|} with hSdef
    have hSm : MeasurableSet S :=
      measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (Lp.stronglyMeasurable g).measurable)
    have hS0 : 0 < μ S := by
      rw [pos_iff_ne_zero]
      intro hS0
      rw [measure_eq_zero_iff_ae_notMem] at hS0
      have hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ c' := by
        filter_upwards [hS0] with x hx
        simpa [hSdef, Real.norm_eq_abs] using hx
      have : eLpNorm g ∞ μ ≤ ENNReal.ofReal c' := by
        rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
        exact eLpNormEssSup_le_of_ae_bound hb
      have := ENNReal.toReal_le_of_le_ofReal (by linarith) this
      rw [← Lp.norm_def] at this
      linarith
    obtain ⟨T, hTm, hTS, hT0, hTfin⟩ := Measure.exists_subset_measure_lt_top hSm hS0
    have hc'0 : 0 ≤ c' := by linarith
    have hgT : ∀ x ∈ T, c' < |g x| := fun x hx => hTS hx
    set k : X → ℝ := T.indicator fun x => Real.sign (g x) with hkdef
    have hkm : AEStronglyMeasurable k μ :=
      ((dualLp_measurable_sign.comp (Lp.stronglyMeasurable g).measurable).indicator
        hTm).aestronglyMeasurable
    have hk : MemLp k 1 μ := by
      refine (memLp_indicator_const 1 hTm (1 : ℝ) (Or.inr hTfin.ne)).mono hkm
        (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ T
      · simp [hkdef, hx, Real.norm_eq_abs, dualLp_abs_sign_le]
      · simp [hkdef, hx]
    have hkg : ∀ x, c' * ‖k x‖ ≤ k x * g x := by
      intro x
      by_cases hx : x ∈ T
      · simp only [hkdef, Set.indicator_of_mem hx, dualLp_sign_mul, Real.norm_eq_abs]
        calc c' * |Real.sign (g x)| ≤ c' * 1 :=
              mul_le_mul_of_nonneg_left (dualLp_abs_sign_le _) hc'0
          _ ≤ |g x| := by rw [mul_one]; exact (hgT x hx).le
      · simp [hkdef, hx]
    have hint : Integrable (fun x => k x * g x) μ :=
      (th_HolderIneq (by simp) hk (Lp.memLp g)).1
    have hkint : Integrable k μ := memLp_one_iff_integrable.1 hk
    have hnorm : ‖hk.toLp k‖ = ∫ x, ‖k x‖ ∂μ := by
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hk] with x hx
      rw [hx]
    have hpos : 0 < ‖hk.toLp k‖ := by
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_pos ?_ hk.eLpNorm_ne_top
      intro h0
      rw [eLpNorm_eq_zero_iff one_ne_zero, EventuallyEq, ae_iff] at h0
      refine hT0.ne' (measure_mono_null (fun x hx => ?_) h0)
      have hgx : g x ≠ 0 := by
        intro h; have := hgT x hx; rw [h, abs_zero] at this; linarith
      simp only [Set.mem_ofPred_eq, hkdef, Set.indicator_of_mem hx, Pi.zero_apply]
      exact fun h => hgx (Real.sign_eq_zero_iff.1 h)
    have h1 : c' * ‖hk.toLp k‖ ≤ dualLp μ 1 ∞ g (hk.toLp k) := by
      rw [dualLp_apply, hnorm, ← integral_const_mul]
      calc ∫ x, c' * ‖k x‖ ∂μ ≤ ∫ x, k x * g x ∂μ :=
            integral_mono (hkint.norm.const_mul c') hint hkg
        _ = ∫ x, hk.toLp k x * g x ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [MemLp.coeFn_toLp hk] with x hx
          rw [hx]
    have h3 : dualLp μ 1 ∞ g (hk.toLp k) ≤ c * ‖hk.toLp k‖ :=
      calc dualLp μ 1 ∞ g (hk.toLp k) ≤ ‖dualLp μ 1 ∞ g (hk.toLp k)‖ := Real.le_norm_self _
        _ ≤ c * ‖hk.toLp k‖ := ContinuousLinearMap.le_opNorm _ _
    have := le_of_mul_le_mul_right (h1.trans h3) hpos
    linarith
  · -- `p = ∞`, `q = 1` : on teste sur `sign(g)`.
    set k : X → ℝ := fun x => Real.sign (g x) with hkdef
    have hkm : AEStronglyMeasurable k μ :=
      (dualLp_measurable_sign.comp (Lp.stronglyMeasurable g).measurable).aestronglyMeasurable
    have hkb : ∀ᵐ x ∂μ, ‖k x‖ ≤ 1 :=
      ae_of_all _ fun x => by simpa [hkdef, Real.norm_eq_abs] using dualLp_abs_sign_le (g x)
    have hk : MemLp k ∞ μ := memLp_top_of_bound hkm 1 hkb
    have hk1 : ‖hk.toLp k‖ ≤ 1 := by
      rw [Lp.norm_toLp]
      refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
      rw [eLpNorm_exponent_top hkm]; exact eLpNormEssSup_le_of_ae_bound hkb
    have h1 : ‖g‖ = dualLp μ ∞ 1 g (hk.toLp k) := by
      rw [dualLp_apply, L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp hk] with x hx
      rw [hx, hkdef, dualLp_sign_mul, Real.norm_eq_abs]
    calc ‖g‖ = dualLp μ ∞ 1 g (hk.toLp k) := h1
      _ ≤ ‖dualLp μ ∞ 1 g (hk.toLp k)‖ := Real.le_norm_self _
      _ ≤ ‖dualLp μ ∞ 1 g‖ * ‖hk.toLp k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖dualLp μ ∞ 1 g‖ * 1 := mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)
      _ = ‖dualLp μ ∞ 1 g‖ := mul_one _
  · -- `1 < p < ∞` : cas d'égalité de Hölder.
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    obtain ⟨k, hk0, hkg⟩ := dualLp_exists_eq_Lp hpq hp1 hp2 hq1 hq2 g hg
    have hk : 0 < ‖k‖ := norm_pos_iff.2 hk0
    have : ‖k‖ * ‖g‖ ≤ ‖k‖ * ‖dualLp μ p q g‖ :=
      calc ‖k‖ * ‖g‖ = dualLp μ p q g k := by rw [dualLp_apply, hkg]
        _ ≤ ‖dualLp μ p q g k‖ := Real.le_norm_self _
        _ ≤ ‖dualLp μ p q g‖ * ‖k‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖k‖ * ‖dualLp μ p q g‖ := mul_comm _ _
    exact le_of_mul_le_mul_left this hk

/-- Pour `2 ≤ p < ∞`, `L^p` est uniformément convexe (Clarkson), donc réflexif
(Milman–Pettis). -/
private lemma dualLp_reflexif_two {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 2 ≤ p) (hp' : p ≠ ∞) :
    Reflexif (Lp ℝ p μ) := by
  have := prop_ClarksonIneq_unifCvx (μ := μ) hp hp'
  exact th_unifCvxReflex_uniformConvexSpace

/-- Si `L^p` est réflexif (`1 < p < ∞`), alors `g ↦ φ_g` est surjective : sinon une forme
`ψ = Φ(f) ∈ (L^p)^{**}` non nulle s'annule sur l'image (fermée), ce que contredit le cas
d'égalité de Hölder. -/
private lemma dualLp_surj_of_reflexif {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [q.HolderConjugate p] (hp : 1 < p) (hp' : p ≠ ∞) (hR : Reflexif (Lp ℝ p μ)) :
    Function.Surjective (dualLp μ p q) := by
  have hqp : q⁻¹ + p⁻¹ = 1 := by
    simpa using (‹q.HolderConjugate p› : ENNReal.HolderTriple q p 1).inv_add_inv_eq_inv
  obtain ⟨hp1, hp2, hq1, hq2⟩ : 1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ := by
    rcases dualLp_conj_cases (p := p) (q := q) with h | h | h
    · exact absurd h.1 hp.ne'
    · exact absurd h.1 hp'
    · exact h
  have hiso := th_lpDualLq_isometrie (μ := μ) (p := p) (q := q) (fun h => absurd h hp.ne')
  set T := dualLp μ p q with hT
  set F := LinearMap.range (T : Lp ℝ q μ →ₗ[ℝ] StrongDual ℝ (Lp ℝ p μ)) with hF
  have hFset : (F : Set (StrongDual ℝ (Lp ℝ p μ))) = Set.range T := LinearMap.coe_range _
  have hFc : IsClosed (F : Set (StrongDual ℝ (Lp ℝ p μ))) := by
    rw [hFset]; exact hiso.isClosedEmbedding.isClosed_range
  intro φ
  by_contra hφ
  have hφF : φ ∉ (F : Set (StrongDual ℝ (Lp ℝ p μ))) := by
    rw [hFset]; exact hφ
  obtain ⟨ψ, u, hψφ, hψF⟩ := geometric_hahn_banach_point_closed F.convex hFc hφF
  have hvan : ∀ g, ψ (T g) = 0 := by
    intro g
    by_contra hne
    have := hψF (T (((u - 1) / ψ (T g)) • g)) (by rw [hFset]; exact Set.mem_range_self _)
    rw [map_smul, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
    linarith
  have hu : u < 0 := by
    have := hψF (T 0) (by rw [hFset]; exact Set.mem_range_self _)
    rwa [map_zero, map_zero] at this
  obtain ⟨f, hf⟩ := hR.2 ψ
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    rw [← hf] at hψφ
    simp at hψφ
    linarith
  obtain ⟨k, hk0, hkf⟩ := dualLp_exists_eq_Lp hqp hq1 hq2 hp1 hp2 f hf0
  have h1 : ψ (T k) = ∫ x, k x * f x ∂μ := by
    rw [← hf, def_reflexif_eval, hT, dualLp_apply]
    simp_rw [mul_comm]
  rw [hvan, hkf] at h1
  exact mul_ne_zero (norm_ne_zero_iff.2 hk0) (norm_ne_zero_iff.2 hf0) h1.symm

/-- **Th. `th:lpDualLq` (Dualité dans les espaces de Lebesgue), bijectivité.** Pour
`1 < p < ∞`, l'application `g ∈ L^q ↦ φ_g ∈ (L^p)^*` est bijective. Si `2 ≤ p`, `L^p` est
uniformément convexe donc réflexif, et une forme de `(L^p)^{**}` s'annulant sur l'image
(fermée) est nulle par le cas d'égalité de Hölder ; si `p < 2`, on utilise
`L^q(X,μ)^* = L^p(X,μ)` avec `q > 2` et la réflexivité de `L^q`. -/
theorem th_lpDualLq_bijectif {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [q.HolderConjugate p]
    (hp : 1 < p) (hp' : p ≠ ∞) : Function.Bijective (dualLp μ p q) := by
  have hqp : q⁻¹ + p⁻¹ = 1 := by
    simpa using (‹q.HolderConjugate p› : ENNReal.HolderTriple q p 1).inv_add_inv_eq_inv
  obtain ⟨hp1, hp2, hq1, hq2⟩ : 1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ := by
    rcases dualLp_conj_cases (p := p) (q := q) with h | h | h
    · exact absurd h.1 hp.ne'
    · exact absurd h.1 hp'
    · exact h
  refine ⟨(th_lpDualLq_isometrie (fun h => absurd h hp.ne')).injective, ?_⟩
  rcases le_or_gt 2 p with h2 | h2
  · exact dualLp_surj_of_reflexif hp hp' (dualLp_reflexif_two h2 hp')
  -- `1 < p < 2` : alors `q > 2`, `L^q` est réflexif et `S : L^p → (L^q)^*` est bijective.
  have hq2' : 2 ≤ q := by
    by_contra hlt
    push Not at hlt
    have h1 : 2⁻¹ < q⁻¹ := ENNReal.inv_lt_inv.2 hlt
    have h2' : 2⁻¹ < p⁻¹ := ENNReal.inv_lt_inv.2 h2
    have := ENNReal.add_lt_add h1 h2'
    rw [hqp, ENNReal.inv_two_add_inv_two] at this
    exact lt_irrefl _ this
  have : p.HolderConjugate q := ‹q.HolderConjugate p›.symm
  have hRq := dualLp_reflexif_two (μ := μ) hq2' hq2.ne
  have hSs := dualLp_surj_of_reflexif (μ := μ) (p := q) (q := p) hq1 hq2.ne hRq
  have hSi := th_lpDualLq_isometrie (μ := μ) (p := q) (q := p) (fun h => absurd h hq1.ne')
  set S := dualLp μ q p with hS
  let e : Lp ℝ p μ ≃ₗᵢ[ℝ] StrongDual ℝ (Lp ℝ q μ) :=
    LinearIsometryEquiv.ofSurjective ⟨S.toLinearMap, fun x => hSi.norm_map_of_map_zero
      (map_zero S) x⟩ hSs
  intro φ
  obtain ⟨g, hg⟩ := hRq.2 (φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨g, ContinuousLinearMap.ext fun h => ?_⟩
  have := congrArg (fun ζ : StrongDual ℝ (StrongDual ℝ (Lp ℝ q μ)) => ζ (e h)) hg
  simp only [def_reflexif_eval, ContinuousLinearMap.comp_apply] at this
  rw [dualLp_apply]
  change ∫ x, h x * g x ∂μ = φ h
  have he : e h = S h := rfl
  rw [show e.symm.toContinuousLinearEquiv.toContinuousLinearMap (e h) = h from
    e.symm_apply_apply h, he, hS, dualLp_apply] at this
  rw [← this]
  simp_rw [mul_comm]

/-- **Réflexivité des espaces de Lebesgue.** Pour `1 < p < ∞`, `L^p(X,μ)` est réflexif :
pour `p ≥ 2` par uniforme convexité (Clarkson, Milman–Pettis), et pour `p < 2` via les
identifications `L^p(X,μ)^* = L^q(X,μ)` et `L^q(X,μ)^* = L^p(X,μ)`. -/
theorem reflexif_Lp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    Reflexif (Lp ℝ p μ) := by
  rcases le_or_gt 2 p with h2 | h2
  · exact dualLp_reflexif_two h2 hp'
  set q := ENNReal.conjExponent p with hq
  have : q.HolderConjugate p := (inferInstance : p.HolderConjugate q).symm
  have hq1' : 1 ≤ q := by
    rcases dualLp_conj_cases (p := p) (q := q) with h | h | h
    · rw [h.2]; exact le_top
    · rw [h.2]
    · exact h.2.2.1.le
  have : Fact (1 ≤ q) := ⟨hq1'⟩
  obtain ⟨hp1, hp2, hq1, hq2⟩ : 1 < p ∧ p < ∞ ∧ 1 < q ∧ q < ∞ := by
    rcases dualLp_conj_cases (p := p) (q := q) with h | h | h
    · exact absurd h.1 hp.ne'
    · exact absurd h.1 hp'
    · exact h
  have hT := th_lpDualLq_bijectif (μ := μ) (p := p) (q := q) hp hp'
  have hS := th_lpDualLq_bijectif (μ := μ) (p := q) (q := p) hq1 hq2.ne
  refine (def_reflexif_iff_surjective _).2 fun ψ => ?_
  obtain ⟨f, hf⟩ := hS.2 (ψ.comp (dualLp μ p q))
  refine ⟨f, ContinuousLinearMap.ext fun φ => ?_⟩
  obtain ⟨g, rfl⟩ := hT.2 φ
  have := congrArg (fun θ : StrongDual ℝ (Lp ℝ q μ) => θ g) hf
  simp only [ContinuousLinearMap.comp_apply] at this
  rw [def_reflexif_eval, ← this, dualLp_apply, dualLp_apply]
  simp_rw [mul_comm]

end Lebesgue

section L1

open Set

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Poids strictement positif de carré intégrable (mesure σ-finie). -/
private lemma dualL1_exists_weight [SigmaFinite μ] :
    ∃ u : X → ℝ, Measurable u ∧ (∀ x, 0 < u x) ∧ MemLp u 2 μ := by
  obtain ⟨w, hw0, hwm, hwi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μ one_ne_zero
  have hwm' : Measurable fun x => (w x : ℝ) := hwm.coe_nnreal_real
  refine ⟨fun x => Real.sqrt (w x), hwm'.sqrt,
    fun x => Real.sqrt_pos.2 (by exact_mod_cast hw0 x), ?_⟩
  rw [memLp_two_iff_integrable_sq hwm'.sqrt.aestronglyMeasurable]
  simp_rw [Real.sq_sqrt (NNReal.coe_nonneg _)]
  have := integrable_toReal_of_lintegral_ne_top hwm.coe_nnreal_ennreal.aemeasurable
    (hwi.trans ENNReal.one_lt_top).ne
  simpa using this

/-- Représentation de Riesz de `k ↦ φ(k u)` sur `L^2`. -/
private lemma dualL1_riesz {u : X → ℝ} (hu : MemLp u 2 μ) (φ : StrongDual ℝ (Lp ℝ 1 μ)) :
    ∃ h : Lp ℝ 2 μ, ∀ (k : X → ℝ), MemLp k 2 μ → ∀ F : Lp ℝ 1 μ,
      (F : X → ℝ) =ᵐ[μ] (fun x => k x * u x) → φ F = ∫ x, h x * k x ∂μ := by
  let ι : Lp ℝ 2 μ →L[ℝ] Lp ℝ 1 μ :=
    ((ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1).flip (hu.toLp u)
  refine ⟨(InnerProductSpace.toDual ℝ (Lp ℝ 2 μ)).symm (φ.comp ι), fun k hk F hF => ?_⟩
  have hιF : ι (hk.toLp k) = F := by
    apply Lp.ext
    have h1 := ContinuousLinearMap.coeFn_holder (r := 1) (ContinuousLinearMap.mul ℝ ℝ)
      (hk.toLp k) (hu.toLp u)
    filter_upwards [h1, hk.coeFn_toLp, hu.coeFn_toLp, hF] with x h1 h2 h3 h4
    rw [h4]
    exact h1.trans (by simp [h2, h3])
  rw [← hιF, ← ContinuousLinearMap.comp_apply, ← InnerProductSpace.toDual_symm_apply,
    L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hk.coeFn_toLp] with x hx
  simp [hx, mul_comm]

/-- Borne essentielle : `|h/u| ≤ ‖φ‖ + 1` presque partout. -/
private lemma dualL1_bound {u : X → ℝ} (hum : Measurable u) (hu0 : ∀ x, 0 < u x)
    (hu : MemLp u 2 μ) (φ : StrongDual ℝ (Lp ℝ 1 μ)) (h : Lp ℝ 2 μ)
    (hφ : ∀ (k : X → ℝ), MemLp k 2 μ → ∀ F : Lp ℝ 1 μ,
      (F : X → ℝ) =ᵐ[μ] (fun x => k x * u x) → φ F = ∫ x, h x * k x ∂μ) :
    ∀ᵐ x ∂μ, |h x / u x| ≤ ‖φ‖ + 1 := by
  set g : X → ℝ := fun x => h x / u x with hg
  have hgm : Measurable g := (Lp.stronglyMeasurable h).measurable.div hum
  set c := ‖φ‖ + 1 with hc
  let S : ℕ → Set X := fun n => {x | c < |g x|} ∩ {x | 1 ≤ n * u x}
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (measurableSet_lt measurable_const (continuous_abs.measurable.comp hgm)).inter
      (measurableSet_le measurable_const (measurable_const.mul hum))
  have hu2 : Integrable (fun x => u x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).1 hu
  have hSfin : ∀ n, μ (S n) < ∞ := by
    intro n
    refine (measure_mono fun x hx => ?_).trans_lt
      ((hu2.const_mul ((n : ℝ) ^ 2)).measure_norm_ge_lt_top one_pos)
    have h1 : 1 ≤ (n : ℝ) * u x := hx.2
    change 1 ≤ ‖(n : ℝ) ^ 2 * u x ^ 2‖
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity), ← mul_pow]
    nlinarith
  have hS0 : ∀ n, μ (S n) = 0 := by
    intro n
    let s : X → ℝ := fun x => if 0 ≤ g x then 1 else -1
    have hsm : Measurable s :=
      Measurable.ite (measurableSet_le measurable_const hgm) measurable_const measurable_const
    have hsg : ∀ x, s x * g x = |g x| := by
      intro x
      by_cases hx : 0 ≤ g x
      · simp [s, hx, abs_of_nonneg hx]
      · simp [s, hx, abs_of_neg (not_le.1 hx)]
    have hs1 : ∀ x, |s x| = 1 := fun x => by by_cases hx : 0 ≤ g x <;> simp [s, hx]
    let k : X → ℝ := (S n).indicator (fun x => s x / u x)
    have hk : MemLp k 2 μ := by
      rw [memLp_indicator_iff_restrict (hSm n)]
      have : IsFiniteMeasure (μ.restrict (S n)) := isFiniteMeasure_restrict.2 (hSfin n).ne
      refine MemLp.of_bound (hsm.div hum).aestronglyMeasurable n ?_
      refine ae_restrict_of_forall_mem (hSm n) fun x hx => ?_
      have h1 : 1 ≤ (n : ℝ) * u x := hx.2
      rw [Real.norm_eq_abs, abs_div, hs1, abs_of_pos (hu0 x), div_le_iff₀ (hu0 x)]
      exact h1
    have hku : MemLp (k * u) 1 μ := hk.mul (r := 1) hu
    have hF := hφ k hk (hku.toLp _) hku.coeFn_toLp
    have hpt : ∀ x, h x * k x = (S n).indicator (fun x => |g x|) x := by
      intro x
      by_cases hx : x ∈ S n
      · simp only [k, indicator_of_mem hx, ← hsg]
        simp only [g]
        field_simp [(hu0 x).ne']
      · simp [k, hx]
    have hint : ∫ x, h x * k x ∂μ = ∫ x, (S n).indicator (fun x => |g x|) x ∂μ :=
      integral_congr_ae (ae_of_all _ hpt)
    have hnorm : ‖hku.toLp (k * u)‖ = μ.real (S n) := by
      rw [L1.norm_eq_integral_norm, ← integral_indicator_one (hSm n)]
      refine integral_congr_ae ?_
      filter_upwards [hku.coeFn_toLp] with x hx
      rw [hx]
      by_cases hxS : x ∈ S n
      · simp [k, hxS, hs1, (hu0 x).ne']
      · simp [k, hxS]
    have hlow : c * μ.real (S n) ≤ ∫ x, (S n).indicator (fun x => |g x|) x ∂μ := by
      rw [mul_comm, ← smul_eq_mul, ← integral_indicator_const _ (hSm n)]
      refine integral_mono ?_ ?_ fun x => ?_
      · exact (integrable_indicator_iff (hSm n)).2 (integrableOn_const (hSfin n).ne)
      · exact ((Lp.memLp h).integrable_mul hk).congr (ae_of_all _ hpt)
      · by_cases hx : x ∈ S n
        · simp only [indicator_of_mem hx]; exact hx.1.le
        · simp [hx]
    have hup : φ (hku.toLp (k * u)) ≤ ‖φ‖ * μ.real (S n) := by
      rw [← hnorm]; exact (le_abs_self _).trans (φ.le_opNorm _)
    have hm : μ.real (S n) ≤ 0 := by
      rw [hF, hint] at hup; rw [hc] at hlow; linarith
    exact (measureReal_eq_zero_iff (hSfin n).ne).1 (le_antisymm hm measureReal_nonneg)
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) (measure_iUnion_null hS0))
  obtain ⟨n, hn⟩ := exists_nat_ge (1 / u x)
  refine mem_iUnion.2 ⟨n, not_le.1 hx, ?_⟩
  change 1 ≤ (n : ℝ) * u x
  rwa [div_le_iff₀ (hu0 x)] at hn

/-- **Th. `th:lpDualLq` (Dualité dans les espaces de Lebesgue), bijectivité pour `p = 1`.**
Si `μ` est σ-finie, `g ∈ L^∞ ↦ φ_g ∈ (L^1)^*` est bijective (`(L^1)^* = L^∞`).
Remarque : non démontré dans le cours ; l'hypothèse de σ-finitude est nécessaire
(cf. \claudereport). -/
theorem th_lpDualLq_bijectif_un [SigmaFinite μ] : Function.Bijective (dualLp μ 1 ∞) := by
  refine ⟨(th_lpDualLq_isometrie (p := 1) (q := ∞) fun _ => inferInstance).injective,
    fun φ => ?_⟩
  obtain ⟨u, hum, hu0, hu⟩ := dualL1_exists_weight (μ := μ)
  obtain ⟨h, hφ⟩ := dualL1_riesz hu φ
  have hb := dualL1_bound hum hu0 hu φ h hφ
  set g : X → ℝ := fun x => h x / u x with hg
  have hgm : Measurable g := (Lp.stronglyMeasurable h).measurable.div hum
  have hG : MemLp g ∞ μ :=
    memLp_top_of_bound hgm.aestronglyMeasurable _
      (hb.mono fun x hx => by rw [Real.norm_eq_abs]; exact hx)
  refine ⟨hG.toLp g, ContinuousLinearMap.ext fun F => ?_⟩
  set Φ := φ - dualLp μ 1 ∞ (hG.toLp g) with hΦ
  have hFm : Measurable (F : X → ℝ) := (Lp.stronglyMeasurable F).measurable
  let A : ℕ → Set X := fun n => {x | |F x| ≤ n * u x ^ 2}
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_le (continuous_abs.measurable.comp hFm) (measurable_const.mul (hum.pow_const 2))
  have hFn : ∀ n, MemLp ((A n).indicator F) 1 μ := fun n => (Lp.memLp F).indicator (hAm n)
  have hzero : ∀ n, Φ ((hFn n).toLp _) = 0 := by
    intro n
    let k : X → ℝ := fun x => (A n).indicator F x / u x
    have hk : MemLp k 2 μ := by
      refine (memLp_two_iff_integrable_sq (f := k)
        ((hFm.indicator (hAm n)).div hum).aestronglyMeasurable).2 ?_
      refine (((L1.integrable_coeFn F).norm.const_mul n)).mono'
        (((hFm.indicator (hAm n)).div hum).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun x => ?_)
      by_cases hx : x ∈ A n
      · have hx' : |F x| ≤ n * u x ^ 2 := hx
        have hu2 : 0 < u x ^ 2 := by have := hu0 x; positivity
        simp only [k, indicator_of_mem hx, Real.norm_eq_abs]
        rw [abs_of_nonneg (sq_nonneg _), div_pow, div_le_iff₀ hu2]
        nlinarith [abs_nonneg (F x), sq_abs (F x), mul_le_mul_of_nonneg_left hx' (abs_nonneg (F x))]
      · simp only [k, indicator_of_notMem hx]
        simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero]
        positivity
    have hF := hφ k hk ((hFn n).toLp _) (by
      filter_upwards [(hFn n).coeFn_toLp] with x hx
      rw [hx]
      simp only [k]
      rw [div_mul_cancel₀ _ (hu0 x).ne'])
    simp only [Φ, FunLike.coe_sub, Pi.sub_apply, dualLp_apply, hF, sub_eq_zero]
    refine integral_congr_ae ?_
    filter_upwards [(hFn n).coeFn_toLp, hG.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp only [k, g]
    field_simp [(hu0 x).ne']
  have hT : Filter.Tendsto (fun n => (hFn n).toLp _) Filter.atTop (nhds F) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq : ∀ n, ‖(hFn n).toLp _ - F‖ = ∫ x, ‖(A n).indicator F x - F x‖ ∂μ := by
      intro n
      rw [L1.norm_eq_integral_norm]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub ((hFn n).toLp _) F, (hFn n).coeFn_toLp] with x h1 h2
      rw [h1, Pi.sub_apply, h2]
    simp_rw [heq]
    have := tendsto_integral_of_dominated_convergence (fun x => ‖F x‖)
      (F := fun n x => ‖(A n).indicator F x - F x‖) (f := fun _ => 0)
      (fun n => ((hFm.indicator (hAm n)).sub hFm).norm.aestronglyMeasurable)
      (L1.integrable_coeFn F).norm (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · simpa using this
    · by_cases hx : x ∈ A n <;> simp [hx]
    · have hu2 : 0 < u x ^ 2 := by have := hu0 x; positivity
      obtain ⟨N, hN⟩ := exists_nat_ge (|F x| / u x ^ 2)
      refine tendsto_const_nhds.congr' ((Filter.eventually_ge_atTop N).mono fun n hn => ?_)
      have hxA : x ∈ A n := by
        change |F x| ≤ n * u x ^ 2
        rw [div_le_iff₀ hu2] at hN
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      simp [hxA]
  have hlim := (Φ.continuous.tendsto F).comp hT
  have key : Φ F = 0 :=
    (tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hzero n).symm) hlim).symm
  exact (sub_eq_zero.1 key).symm

end L1

section NonReflex
local notation "ℓ" p => lp (fun _ : ℕ => ℝ) p

private lemma nonReflex_mulFlip_norm_le (_ : ℕ) :
    ‖(ContinuousLinearMap.mul ℝ ℝ).flip‖ ≤ ((1 : NNReal) : ℝ) := by
  simp only [NNReal.coe_one]
  exact (ContinuousLinearMap.opNorm_flip (ContinuousLinearMap.mul ℝ ℝ)).le.trans
    (ContinuousLinearMap.opNorm_mul_le ℝ ℝ)

/-- Accouplement `ℓ^∞ × ℓ¹ → ℝ`, `(y, x) ↦ ∑ x_n y_n`. -/
private noncomputable def nonReflexPairInf : (ℓ ∞) →L[ℝ] StrongDual ℝ (ℓ 1) :=
  lp.dualPairing ∞ 1 (fun _ : ℕ => (ContinuousLinearMap.mul ℝ ℝ).flip)
    (K := 1) nonReflex_mulFlip_norm_le

private lemma nonReflexPairInf_apply (y : ℓ∞) (x : ℓ 1) :
    nonReflexPairInf y x = ∑' n, x n * y n := rfl

private lemma nonReflexPairInf_norm_le (y : ℓ∞) : ‖nonReflexPairInf y‖ ≤ ‖y‖ := by
  refine (nonReflexPairInf.le_opNorm y).trans ?_
  have := lp.norm_dualPairing (p := ∞) (q := 1) (fun _ : ℕ => (ContinuousLinearMap.mul ℝ ℝ).flip)
    (K := 1) nonReflex_mulFlip_norm_le
  simp only [NNReal.coe_one] at this
  exact (mul_le_mul_of_nonneg_right this (norm_nonneg _)).trans (by simp)

/-- Développement de `x ∈ ℓ¹` sur la base `δ_n`. -/
private lemma nonReflex_l1_expand (φ : StrongDual ℝ (ℓ 1)) (x : ℓ 1) :
    HasSum (fun n => x n * φ (lp.single 1 n 1)) (φ x) := by
  have h := (lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := 1) ENNReal.one_ne_top x).mapL φ
  convert h using 2 with n
  have : lp.single 1 n (x n) = x n • (lp.single 1 n (1 : ℝ) : ℓ 1) := by
    rw [← lp.single_smul]; simp
  simp [this]

/-- Une suite tendant vers `0`, vue comme élément de `C₀(ℕ, ℝ)` (`ℕ` est discret). -/
private def nonReflexMkC0 (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) : C₀(ℕ, ℝ) :=
  ⟨⟨f, continuous_of_discreteTopology⟩, by rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop]⟩

private lemma nonReflexMkC0_apply (f : ℕ → ℝ) (hf : Tendsto f atTop (𝓝 0)) (n : ℕ) :
    nonReflexMkC0 f hf n = f n := rfl

private lemma nonReflex_c0_tendsto (x : C₀(ℕ, ℝ)) : Tendsto (fun n => x n) atTop (𝓝 0) := by
  have := x.zero_at_infty'
  rwa [cocompact_eq_cofinite, Nat.cofinite_eq_atTop] at this

private lemma nonReflex_c0_norm_le {x : C₀(ℕ, ℝ)} {C : ℝ} (hC : 0 ≤ C) (h : ∀ n, |x n| ≤ C) :
    ‖x‖ ≤ C := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm, BoundedContinuousFunction.norm_le hC]
  exact h

private lemma nonReflex_c0_apply_le (x : C₀(ℕ, ℝ)) (n : ℕ) : |x n| ≤ ‖x‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm x.toBCF n

/-- Troncature `(f_0, …, f_{N-1}, 0, 0, …)` dans `C₀(ℕ, ℝ)`. -/
private def nonReflexTrunc (f : ℕ → ℝ) (N : ℕ) : C₀(ℕ, ℝ) :=
  nonReflexMkC0 (fun m => if m < N then f m else 0) <| tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop N] with m hm
    simp [not_lt.2 hm]

/-- La suite `δ_n` dans `C₀(ℕ, ℝ)`. -/
private def nonReflexDelta (n : ℕ) : C₀(ℕ, ℝ) :=
  nonReflexMkC0 (fun m => if m = n then 1 else 0) <| tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_gt_atTop n] with m hm
    simp [hm.ne']

private lemma nonReflexTrunc_apply (f : ℕ → ℝ) (N m : ℕ) :
    nonReflexTrunc f N m = if m < N then f m else 0 := rfl

private lemma nonReflexDelta_apply (n m : ℕ) :
    nonReflexDelta n m = if m = n then 1 else 0 := rfl

private lemma nonReflex_map_trunc (φ : StrongDual ℝ C₀(ℕ, ℝ)) (f : ℕ → ℝ) (N : ℕ) :
    φ (nonReflexTrunc f N) = ∑ n ∈ Finset.range N, f n * φ (nonReflexDelta n) := by
  induction N with
  | zero =>
    have : nonReflexTrunc f 0 = 0 := by
      ext m; simp [nonReflexTrunc_apply]
    simp [this]
  | succ N ih =>
    have : nonReflexTrunc f (N + 1) = nonReflexTrunc f N + f N • nonReflexDelta N := by
      ext m
      simp only [nonReflexTrunc_apply, nonReflexDelta_apply, ZeroAtInftyContinuousMap.add_apply,
        ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
      by_cases h1 : m < N
      · simp [h1, (Nat.lt_succ_of_lt h1), h1.ne]
      · by_cases h2 : m = N
        · simp [h2]
        · have : ¬ m < N + 1 := by omega
          simp [h1, h2, this]
    rw [this, map_add, map_smul, ih, Finset.sum_range_succ, smul_eq_mul]

/-- Signe de `t` (avec la convention `+1` en `0`), qui vérifie `s t * t = |t|`. -/
private noncomputable def nonReflexSgn (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

private lemma nonReflexSgn_mul (t : ℝ) : nonReflexSgn t * t = |t| := by
  unfold nonReflexSgn
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (not_le.1 h)]

private lemma nonReflexSgn_abs (t : ℝ) : |nonReflexSgn t| = 1 := by
  unfold nonReflexSgn; split_ifs <;> simp

/-- Astuce du signe : `∑_{n<N} |φ(δ_n)| ≤ ‖φ‖`. -/
private lemma nonReflex_c0_partial (φ : StrongDual ℝ C₀(ℕ, ℝ)) (N : ℕ) :
    ∑ n ∈ Finset.range N, |φ (nonReflexDelta n)| ≤ ‖φ‖ := by
  have h := φ.le_opNorm (nonReflexTrunc (fun n => nonReflexSgn (φ (nonReflexDelta n))) N)
  rw [nonReflex_map_trunc] at h
  simp only [nonReflexSgn_mul] at h
  have hn : ‖nonReflexTrunc (fun n => nonReflexSgn (φ (nonReflexDelta n))) N‖ ≤ 1 := by
    refine nonReflex_c0_norm_le zero_le_one fun m => ?_
    rw [nonReflexTrunc_apply]
    split_ifs <;> simp [nonReflexSgn_abs]
  calc ∑ n ∈ Finset.range N, |φ (nonReflexDelta n)|
      ≤ ‖∑ n ∈ Finset.range N, |φ (nonReflexDelta n)|‖ := le_abs_self _
    _ ≤ _ := h
    _ ≤ ‖φ‖ * 1 := by gcongr
    _ = ‖φ‖ := mul_one _

private lemma nonReflex_c0_summable (φ : StrongDual ℝ C₀(ℕ, ℝ)) :
    Summable fun n => |φ (nonReflexDelta n)| :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (nonReflex_c0_partial φ)

/-- Densité des suites à support fini : `φ(x) = ∑ x_n φ(δ_n)`. -/
private lemma nonReflex_c0_expand (φ : StrongDual ℝ C₀(ℕ, ℝ)) (x : C₀(ℕ, ℝ)) :
    φ x = ∑' n, x n * φ (nonReflexDelta n) := by
  have hs : Summable fun n => x n * φ (nonReflexDelta n) := by
    refine Summable.of_norm_bounded ((nonReflex_c0_summable φ).mul_left ‖x‖) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (nonReflex_c0_apply_le x n) (abs_nonneg _)
  have htr : Tendsto (fun N => nonReflexTrunc (fun n => x n) N) atTop (𝓝 x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (nonReflex_c0_tendsto x) (ε / 2) (by positivity)
    refine ⟨M, fun N hN => ?_⟩
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (nonReflex_c0_norm_le (by positivity) fun m => ?_) (half_lt_self hε)
    rw [ZeroAtInftyContinuousMap.sub_apply, nonReflexTrunc_apply]
    split_ifs with h
    · simp only [sub_self, abs_zero]; positivity
    · have := hM m (by omega)
      rw [Real.dist_eq, sub_zero] at this
      simpa using this.le
  have h1 := (φ.continuous.tendsto x).comp htr
  have h2 : (fun N => φ (nonReflexTrunc (fun n => x n) N)) =
      fun N => ∑ n ∈ Finset.range N, x n * φ (nonReflexDelta n) := by
    funext N; exact nonReflex_map_trunc φ _ N
  exact tendsto_nhds_unique (h2 ▸ h1) hs.hasSum.tendsto_sum_nat

/-- Accouplement `ℓ¹ × ℓ^∞ → ℝ`, `(y, x) ↦ ∑ x_n y_n`. -/
private noncomputable def nonReflexPairOne : (ℓ 1) →L[ℝ] StrongDual ℝ (ℓ ∞) :=
  lp.dualPairing 1 ∞ (fun _ : ℕ => (ContinuousLinearMap.mul ℝ ℝ).flip)
    (K := 1) nonReflex_mulFlip_norm_le

private lemma nonReflexPairOne_norm_le (y : ℓ 1) : ‖nonReflexPairOne y‖ ≤ ‖y‖ := by
  refine (nonReflexPairOne.le_opNorm y).trans ?_
  have := lp.norm_dualPairing (p := 1) (q := ∞) (fun _ : ℕ => (ContinuousLinearMap.mul ℝ ℝ).flip)
    (K := 1) nonReflex_mulFlip_norm_le
  simp only [NNReal.coe_one] at this
  exact (mul_le_mul_of_nonneg_right this (norm_nonneg _)).trans (by simp)

/-- Injection isométrique `C₀(ℕ, ℝ) → ℓ^∞`. -/
private noncomputable def nonReflexJ : C₀(ℕ, ℝ) →L[ℝ] (ℓ ∞) :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun n => x n, memℓp_infty_iff.2 ⟨‖x‖, by
        rintro _ ⟨n, rfl⟩; exact nonReflex_c0_apply_le x n⟩⟩
      map_add' := fun x y => by ext n; rfl
      map_smul' := fun c x => by ext n; rfl } 1 fun x => by
    rw [one_mul]
    exact lp.norm_le_of_forall_le (norm_nonneg _) fun n => nonReflex_c0_apply_le x n

private noncomputable def nonReflexT0 : (ℓ 1) →ₗ[ℝ] StrongDual ℝ C₀(ℕ, ℝ) where
  toFun y := (nonReflexPairOne y).comp nonReflexJ
  map_add' a b := by ext x; simp
  map_smul' c a := by ext x; simp

private lemma nonReflexT0_apply (y : ℓ 1) (x : C₀(ℕ, ℝ)) :
    nonReflexT0 y x = ∑' n, x n * y n := rfl

private lemma nonReflexT0_delta (y : ℓ 1) (n : ℕ) : nonReflexT0 y (nonReflexDelta n) = y n := by
  rw [nonReflexT0_apply, tsum_eq_single n]
  · simp [nonReflexDelta_apply]
  · intro m hm; simp [nonReflexDelta_apply, hm]

/-- Sous-espace des suites convergentes de `ℓ^∞`. -/
private def nonReflexConv : Submodule ℝ (ℓ ∞) where
  carrier := {x | ∃ l, Tendsto (fun n => x n) atTop (𝓝 l)}
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by simpa using ha.add hb⟩
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha⟩
    exact ⟨c * a, by simpa using ha.const_mul c⟩

private lemma nonReflexConv_lim (x : nonReflexConv) :
    Tendsto (fun n => (x : ℓ ∞) n) atTop (𝓝 (limUnder atTop fun n => (x : ℓ ∞) n)) := by
  obtain ⟨l, hl⟩ := x.2
  rwa [hl.limUnder_eq]

/-- La forme linéaire `lim` sur les suites convergentes. -/
private noncomputable def nonReflexLimₗ : nonReflexConv →ₗ[ℝ] ℝ where
  toFun x := limUnder atTop fun n => (x : ℓ ∞) n
  map_add' x y := by
    refine (Tendsto.limUnder_eq ?_)
    simpa using (nonReflexConv_lim x).add (nonReflexConv_lim y)
  map_smul' c x := by
    refine (Tendsto.limUnder_eq ?_)
    simpa using (nonReflexConv_lim x).const_mul c

private noncomputable def nonReflexLim : StrongDual ℝ nonReflexConv :=
  nonReflexLimₗ.mkContinuous 1 fun x => by
    rw [one_mul]
    refine le_of_tendsto' (nonReflexConv_lim x).norm fun n => ?_
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero (x : ℓ ∞) n

private lemma nonReflexLim_eq (x : nonReflexConv) {l : ℝ}
    (h : Tendsto (fun n => (x : ℓ∞) n) atTop (𝓝 l)) : nonReflexLim x = l :=
  h.limUnder_eq

/-- L'indicatrice de `[N, ∞)` dans `ℓ^∞`. -/
private def nonReflexInd (N : ℕ) : ℓ ∞ :=
  ⟨fun n => if N ≤ n then 1 else 0, memℓp_infty_iff.2 ⟨1, by
    rintro _ ⟨n, rfl⟩; dsimp only; split_ifs <;> simp⟩⟩

private lemma nonReflexInd_tendsto (N : ℕ) :
    Tendsto (fun n => nonReflexInd N n) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' <| by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [nonReflexInd, hn]

private lemma nonReflex_l1_summable (y : ℓ 1) : Summable fun n => |y n| := by
  have := (memℓp_gen_iff (p := 1) (by norm_num)).1 y.2
  simpa using this

/-- **Ex. `ex:nonReflex` (dual de `c₀`).** Le dual de `c₀ = C₀(ℕ, ℝ)` s'identifie isométriquement
à `ℓ¹` : à `y ∈ ℓ¹` correspond la forme `x ↦ ∑ x_n y_n`. (On pose `y_n := φ(δ_n)`, astuce du
signe, et densité des suites à support fini.) -/
theorem ex_nonReflex_c0 : ∃ e : (ℓ 1) ≃ₗᵢ[ℝ] StrongDual ℝ C₀(ℕ, ℝ),
    ∀ (y : ℓ 1) (x : C₀(ℕ, ℝ)), e y x = ∑' n, x n * y n := by
  have hiso : ∀ y : ℓ 1, ‖nonReflexT0 y‖ = ‖y‖ := by
    intro y
    refine le_antisymm ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      calc ‖nonReflexT0 y x‖ = ‖nonReflexPairOne y (nonReflexJ x)‖ := rfl
        _ ≤ ‖nonReflexPairOne y‖ * ‖nonReflexJ x‖ := (nonReflexPairOne y).le_opNorm _
        _ ≤ ‖y‖ * ‖x‖ := by
          gcongr
          · exact nonReflexPairOne_norm_le y
          · exact lp.norm_le_of_forall_le (f := nonReflexJ x) (norm_nonneg _)
              fun n => nonReflex_c0_apply_le x n
    · refine lp.norm_le_of_tsum_le (f := y) (by norm_num) (norm_nonneg (nonReflexT0 y)) ?_
      simp only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs]
      refine Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) fun N => ?_
      simpa [nonReflexT0_delta] using nonReflex_c0_partial (nonReflexT0 y) N
  let L : (ℓ 1) →ₗᵢ[ℝ] StrongDual ℝ C₀(ℕ, ℝ) := ⟨nonReflexT0, hiso⟩
  have hsurj : Function.Surjective L := by
    intro φ
    have hmem : Memℓp (fun n => φ (nonReflexDelta n)) 1 := by
      refine memℓp_gen ?_
      simpa using nonReflex_c0_summable φ
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    exact (nonReflex_c0_expand φ x).symm
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, fun y x => rfl⟩

/-- **Ex. `ex:nonReflex` (dual de `ℓ¹`).** Le dual de `ℓ¹` s'identifie isométriquement à `ℓ^∞` :
à `y ∈ ℓ^∞` correspond la forme `x ↦ ∑ x_n y_n`, avec `y_n := φ(δ_n)`. -/
theorem ex_nonReflex_l1 : ∃ e : (ℓ ∞) ≃ₗᵢ[ℝ] StrongDual ℝ (ℓ 1),
    ∀ (y : ℓ ∞) (x : ℓ 1), e y x = ∑' n, x n * y n := by
  have hiso : ∀ y : ℓ ∞, ‖nonReflexPairInf y‖ = ‖y‖ := by
    intro y
    refine le_antisymm (nonReflexPairInf_norm_le y) ?_
    refine lp.norm_le_of_forall_le (norm_nonneg _) fun n => ?_
    have h := (nonReflexPairInf y).le_opNorm (lp.single 1 n 1)
    have h1 : nonReflexPairInf y (lp.single 1 n 1) = y n := by
      rw [nonReflexPairInf_apply, tsum_eq_single n]
      · simp
      · intro m hm; rw [lp.single_apply_ne 1 n _ hm, zero_mul]
    rw [h1, lp.norm_single (by norm_num)] at h
    simpa using h
  let L : (ℓ ∞) →ₗᵢ[ℝ] StrongDual ℝ (ℓ 1) := ⟨nonReflexPairInf.toLinearMap, hiso⟩
  have hsurj : Function.Surjective L := by
    intro φ
    have hmem : Memℓp (fun n => φ (lp.single 1 n (1 : ℝ))) ∞ := by
      refine memℓp_infty_iff.2 ⟨‖φ‖, ?_⟩
      rintro _ ⟨n, rfl⟩
      have := φ.le_opNorm (lp.single 1 n 1)
      rwa [lp.norm_single (by norm_num), norm_one, mul_one] at this
    refine ⟨⟨_, hmem⟩, ?_⟩
    ext x
    exact ((nonReflex_l1_expand φ x).tsum_eq).symm.trans rfl |>.symm
  exact ⟨LinearIsometryEquiv.ofSurjective L hsurj, fun y x => rfl⟩

/-- **Ex. `ex:nonReflex` (forme limite).** Il existe `φ ∈ (ℓ^∞)^*` de norme `1` qui coïncide avec
`lim` sur les suites convergentes (prolongement de Hahn–Banach), et qui n'est pas de la forme
`x ↦ ∑ x_n y_n` avec `y ∈ ℓ¹` : sinon, en testant sur l'indicatrice de `[N, ∞)`, on aurait
`∑_{n ≥ N} y_n = 1` pour tout `N`, ce qui est impossible. -/
theorem ex_nonReflex_lim : ∃ φ : StrongDual ℝ (ℓ ∞), ‖φ‖ = 1 ∧
    (∀ (x : ℓ ∞) (l : ℝ), Tendsto (fun n => x n) atTop (𝓝 l) → φ x = l) ∧
    ¬ ∃ y : ℓ 1, ∀ x : ℓ ∞, φ x = ∑' n, x n * y n := by
  obtain ⟨φ, hφ, hnorm⟩ := exists_extension_norm_eq nonReflexConv nonReflexLim
  have hφl : ∀ (x : ℓ ∞) (l : ℝ), Tendsto (fun n => x n) atTop (𝓝 l) → φ x = l :=
    fun x l h => (hφ ⟨x, l, h⟩).trans (nonReflexLim_eq ⟨x, l, h⟩ h)
  refine ⟨φ, le_antisymm ?_ ?_, hφl, ?_⟩
  · rw [hnorm]; exact LinearMap.mkContinuous_norm_le _ zero_le_one _
  · have h1 := φ.le_opNorm (nonReflexInd 0)
    rw [hφl _ 1 (nonReflexInd_tendsto 0)] at h1
    have h2 : ‖nonReflexInd 0‖ ≤ 1 :=
      lp.norm_le_of_forall_le zero_le_one fun n => by simp [nonReflexInd]
    have := h1.trans (mul_le_of_le_one_right (norm_nonneg _) h2)
    simpa using this
  · rintro ⟨y, hy⟩
    have hconst : ∀ N, ∑' k, y (k + N) = 1 := by
      intro N
      have hs : Summable fun n => nonReflexInd N n * y n := by
        refine Summable.of_norm_bounded (nonReflex_l1_summable y) fun n => ?_
        rw [Real.norm_eq_abs, abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        simp only [nonReflexInd]; split_ifs <;> simp
      rw [← hφl _ 1 (nonReflexInd_tendsto N), hy, ← hs.sum_add_tsum_nat_add N]
      have h0 : ∑ i ∈ Finset.range N, nonReflexInd N i * y i = 0 :=
        Finset.sum_eq_zero fun i hi => by
          simp [nonReflexInd, not_le.2 (Finset.mem_range.1 hi)]
      rw [h0, zero_add]
      congr 1; funext k; simp [nonReflexInd]
    have := tendsto_sum_nat_add fun n => y n
    simp only [hconst] at this
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds this)

/-- **Ex. `ex:nonReflex` (non-réflexivité de `ℓ¹`).** L'espace `ℓ¹` n'est pas réflexif : si `Φ`
était surjective, `φ ∘ e⁻¹ ∈ (ℓ¹)^{**}` serait l'évaluation en un `y ∈ ℓ¹`, ce qui contredit
`ex_nonReflex_lim`. -/
theorem ex_nonReflex_l1_nonReflexif : ¬ Reflexif (ℓ 1) := by
  intro h
  rw [def_reflexif_iff_surjective] at h
  obtain ⟨e, he⟩ := ex_nonReflex_l1
  obtain ⟨φ, -, -, hφ⟩ := ex_nonReflex_lim
  obtain ⟨y, hy⟩ := h (φ.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  refine hφ ⟨y, fun x => ?_⟩
  have := congrArg (fun F => F (e x)) hy
  simp only [def_reflexif_eval, he, ContinuousLinearMap.comp_apply] at this
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply] at this
  rw [← this]
  simp only [mul_comm]
end NonReflex

end M1Analyse
