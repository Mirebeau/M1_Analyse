/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import M1Analyse.Bosse.Bosse
import M1Analyse.LegendreFenchel.LegendreFenchel

/-!
# §5.1 Convolution dans les espaces `L^p` (`subsec:convLp`)

Source : `Include/Sobolev.tex`, introduction de la section des espaces de Sobolev et
sous-section `subsec:convLp`.

Les espaces `L^p` du cours sont ceux de Mathlib (`MemLp`, `eLpNorm`), la convolution est
`MeasureTheory.convolution` (`f ⋆[lsmul ℝ ℝ, volume] g`, de formule
`(f ⋆ g)(x) = ∫ f(h) g(x - h) dh`), et `ℝ^d` est `EuclideanSpace ℝ (Fin d)` muni de la mesure
de Lebesgue `volume`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Convolution Distributions
open ContinuousLinearMap (lsmul)

namespace M1Analyse

/-! ### Densité des fonctions continues à support compact -/

section DensC0Lp

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Prop. `prop:densC0Lp` (Densité dans `L^p` des fonctions continues à support compact).**
Soit `X` un espace métrique localement compact, muni d'une mesure borélienne `μ` régulière au
sens du cours `eqdef:mes_reguliere` : régulière intérieurement pour les compacts sur tout
mesurable (`μ.InnerRegular`) et régulière extérieurement (`μ.OuterRegular`). Alors `C^0_c(X)`
est dense dans `L^p(X, μ)` pour `p < ∞` : pour toute `f ∈ L^p` et tout `ε > 0`, il existe `g`
continue à support compact avec `‖f - g‖_p ≤ ε`.
Remarque : l'hypothèse `1 ≤ p` du cours est superflue. (Preuve : celle de Mathlib pour
`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, qui suppose `μ.Regular`, adaptée aux
hypothèses du cours, qui n'imposent pas la finitude de `μ` sur les compacts.) -/
theorem prop_densC0Lp (μ : Measure X) [μ.InnerRegular] [μ.OuterRegular] {p : ℝ≥0∞}
    (hp : p ≠ ∞) {f : X → E} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : X → E, Continuous g ∧ HasCompactSupport g ∧ MemLp g p μ ∧
      eLpNorm (f - g) p μ ≤ ε := by
  suffices H :
      ∃ g : X → E, eLpNorm (f - g) p μ ≤ ε ∧ Continuous g ∧ MemLp g p μ ∧ HasCompactSupport g by
    rcases H with ⟨g, hg, g_cont, g_mem, g_support⟩
    exact ⟨g, g_cont, g_support, g_mem, hg⟩
  apply hf.induction_dense hp _ _ _ hε
  rotate_left
  · rintro f g ⟨f_cont, f_mem, hf⟩ ⟨g_cont, g_mem, hg⟩
    exact ⟨f_cont.add g_cont, f_mem.add g_mem, hf.add hg⟩
  intro c t ht htμ ε hε
  rcases exists_Lp_half E μ p hε with ⟨δ, δpos, hδ⟩
  obtain ⟨η, ηpos, hη⟩ :
      ∃ η : ℝ≥0, 0 < η ∧ ∀ s : Set X, μ s ≤ η → NullMeasurableSet s μ →
          eLpNorm (s.indicator fun _x => c) p μ ≤ δ :=
    exists_eLpNorm_indicator_le hp c δpos.ne'
  have hη_pos' : (0 : ℝ≥0∞) < η := ENNReal.coe_pos.2 ηpos
  obtain ⟨s, st, s_compact, s_closed, μs⟩ :
      ∃ s, s ⊆ t ∧ IsCompact s ∧ IsClosed s ∧ μ (t \ s) < η :=
    ht.exists_isCompact_isClosed_sdiff_lt htμ.ne hη_pos'.ne'
  have hsμ : μ s < ∞ := (measure_mono st).trans_lt htμ
  have I1 : eLpNorm ((s.indicator fun _y => c) - t.indicator fun _y => c) p μ ≤ δ := by
    rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff st]
    exact hη _ μs.le (ht.diff s_closed.measurableSet).nullMeasurableSet
  obtain ⟨k, k_compact, sk⟩ : ∃ k : Set X, IsCompact k ∧ s ⊆ interior k :=
    exists_compact_superset s_compact
  rcases exists_continuous_eLpNorm_sub_le_of_closed hp s_closed isOpen_interior sk hsμ.ne c
    δpos.ne' with ⟨f, f_cont, I2, _f_bound, f_support, f_mem⟩
  have I3 : eLpNorm (f - t.indicator fun _y => c) p μ ≤ ε := by
    convert! (hδ _ _ I2 I1).le using 2
    ext x
    simp
  refine ⟨f, I3, f_cont, f_mem, HasCompactSupport.intro k_compact fun x hx => ?_⟩
  rw [← Function.notMem_support]
  contrapose hx
  exact interior_subset (f_support hx)

end DensC0Lp

/-! ### Inégalité de Jensen et inclusions `L^q ⊂ L^p` -/

section Jensen

variable {X : Type*} [MeasurableSpace X]

/-- Intégrale de Lebesgue d'une fonction `h : X → ℝ̄`, au sens usuel :
`∫ h dμ := ∫ h⁺ dμ - ∫ h⁻ dμ ∈ ℝ̄`, où `h⁺ = max(h, 0)` et `h⁻ = max(-h, 0)` sont intégrées
par l'intégrale de Lebesgue des fonctions positives (`lintegral`, à valeurs dans `[0, ∞]`).
Remarque : bien définie (sans forme `∞ - ∞`) dès que l'une des deux intégrales est finie ;
dans le cas `∞ - ∞`, la soustraction de `EReal` donne la valeur conventionnelle `-∞`
(sans objet ici : voir `integraleEtendue_comp_bienDefinie`). -/
noncomputable def integraleEtendue (μ : Measure X) (h : X → EReal) : EReal :=
  ((∫⁻ x, (h x).toENNReal ∂μ : ℝ≥0∞) : EReal) - ((∫⁻ x, (-h x).toENNReal ∂μ : ℝ≥0∞) : EReal)

/-- Pour `u : X → ℝ` intégrable, `integraleEtendue` coïncide avec l'intégrale de Bochner. -/
theorem integraleEtendue_coe {μ : Measure X} {u : X → ℝ} (hu : Integrable u μ) :
    integraleEtendue μ (fun x => (u x : EReal)) = ((∫ x, u x ∂μ : ℝ) : EReal) := by
  have h1 : (∫⁻ x, ENNReal.ofReal (u x) ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_of_le_toReal
      (by simpa using le_abs_self (u x))) hu.2).ne
  have h2 : (∫⁻ x, ENNReal.ofReal (-u x) ∂μ) ≠ ⊤ :=
    (lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_of_le_toReal
      (by simpa using neg_le_abs (u x))) hu.2).ne
  simp only [integraleEtendue, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hu, EReal.coe_sub,
    ← EReal.coe_ennreal_toReal h1, ← EReal.coe_ennreal_toReal h2]

/-- Monotonie : si `u ≤ h` avec `u : X → ℝ` intégrable, alors `∫ u dμ ≤ ∫ h dμ` dans `ℝ̄`. -/
theorem integral_le_integraleEtendue {μ : Measure X} {u : X → ℝ} (hu : Integrable u μ)
    {h : X → EReal} (huh : ∀ x, (u x : EReal) ≤ h x) :
    ((∫ x, u x ∂μ : ℝ) : EReal) ≤ integraleEtendue μ h := by
  rw [← integraleEtendue_coe hu]
  refine EReal.sub_le_sub ?_ ?_
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (huh x))
  · exact EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (huh x)))

variable {d : ℕ}

/-- **Point technique (Intégrale d'une fonction convexe s.c.i.).** Si `g : ℝ^d → ]-∞, ∞]` est
convexe s.c.i. et `f` intégrable sur un espace de mesure finie, alors `g ∘ f` est (presque)
mesurable et sa partie négative est d'intégrale finie (`g` est minorée par une fonction
affine), de sorte que `∫ g ∘ f dμ ∈ ]-∞, ∞]` est bien définie. Le cours utilise cette
intégrale sans justifier qu'elle a un sens. Utilisé pour `prop:Jensen`. -/
theorem integraleEtendue_comp_bienDefinie {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → EuclideanSpace ℝ (Fin d)} (hf : Integrable f μ)
    {g : EuclideanSpace ℝ (Fin d) → EReal} (hbot : ∀ y, g y ≠ ⊥) (hc : ConvexeEtendue g)
    (hl : LowerSemicontinuous g) :
    AEMeasurable (fun x => g (f x)) μ ∧ ∫⁻ x, (-g (f x)).toENNReal ∂μ < ⊤ ∧
      ⊥ < integraleEtendue μ (fun x => g (f x)) := by
  refine ⟨hl.measurable.comp_aemeasurable hf.aemeasurable, ?_⟩
  obtain ⟨t, -, ht⟩ := EReal.lt_iff_exists_real_btwn.mp (bot_lt_iff_ne_bot.mpr (hbot 0))
  obtain ⟨α, φ, hφ, -⟩ := lem_minorantCvxSci g hbot hc hl 0 t ht
  have hu : Integrable (fun x => α + φ (f x)) μ := (integrable_const α).add (φ.integrable_comp hf)
  refine ⟨lt_of_le_of_lt (lintegral_mono fun x => ?_) hu.2, lt_of_lt_of_le (EReal.bot_lt_coe _)
    (integral_le_integraleEtendue hu (h := fun x => g (f x)) fun x => (hφ (f x)).le)⟩
  calc (-g (f x)).toENNReal ≤ ((-(α + φ (f x)) : ℝ) : EReal).toENNReal :=
        EReal.toENNReal_le_toENNReal
          (by rw [EReal.coe_neg]; exact EReal.neg_le_neg_iff.mpr (hφ (f x)).le)
    _ ≤ ‖α + φ (f x)‖ₑ := by
        rw [EReal.real_coe_toENNReal]
        exact ENNReal.ofReal_le_of_le_toReal (by simpa using neg_le_abs (α + φ (f x)))

/-- **Prop. `prop:Jensen` (Inégalité de Jensen).** Soit `(X, μ)` un espace probabilisé, soit
`f : X → ℝ^d` intégrable, et soit `g : ℝ^d → ]-∞, ∞]` convexe et s.c.i. Alors
`g(∫_X f dμ) ≤ ∫_X g(f(x)) dμ(x)`.
Encodage : `g : ℝ^d → ℝ̄` avec `g ≠ -∞` partout (espace d'arrivée `]-∞, ∞]`), convexité au
sens du sur-graphe (`ConvexeEtendue`) ; l'intégrale de droite est l'intégrale de Lebesgue dans
`ℝ̄` (`integraleEtendue`, `∫ (g∘f)⁺ - ∫ (g∘f)⁻`), bien définie dans `]-∞, ∞]`
(`integraleEtendue_comp_bienDefinie`) ; si elle vaut `+∞`, l'inégalité est triviale. -/
theorem prop_Jensen {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → EuclideanSpace ℝ (Fin d)} (hf : Integrable f μ)
    {g : EuclideanSpace ℝ (Fin d) → EReal} (hbot : ∀ y, g y ≠ ⊥) (hc : ConvexeEtendue g)
    (hl : LowerSemicontinuous g) :
    g (∫ x, f x ∂μ) ≤ integraleEtendue μ (fun x => g (f x)) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨t, ht₁, ht₂⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨α, φ, hφ, hαt⟩ := lem_minorantCvxSci g hbot hc hl (∫ x, f x ∂μ) t ht₂
  have hu : Integrable (fun x => α + φ (f x)) μ := (integrable_const α).add (φ.integrable_comp hf)
  have hint : ∫ x, (α + φ (f x)) ∂μ = α + φ (∫ x, f x ∂μ) := by
    rw [integral_add (integrable_const α) (φ.integrable_comp hf), φ.integral_comp_comm hf]
    simp
  have := integral_le_integraleEtendue hu (h := fun x => g (f x)) fun x => (hφ (f x)).le
  rw [hint] at this
  exact absurd (lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hαt) this) (not_lt.mpr ht₁.le)

/-- La version réelle (ancienne `prop_Jensen`) est un cas particulier : pour `g : ℝ^d → ℝ`
convexe et `g ∘ f` intégrable, `g(∫ f dμ) ≤ ∫ g ∘ f dμ` (intégrale de Bochner). -/
theorem prop_Jensen_reel {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → EuclideanSpace ℝ (Fin d)} (hf : Integrable f μ)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hgf : Integrable (g ∘ f) μ) :
    g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  have hcont : Continuous g := continuousOn_univ.mp (hg.continuousOn isOpen_univ)
  have := prop_Jensen hf (g := fun y => (g y : EReal)) (fun _ => EReal.coe_ne_bot _)
    ((convexeEtendue_coe_iff g).mpr hg)
    (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  rw [integraleEtendue_coe (u := fun x => g (f x)) hgf] at this
  exact_mod_cast this

end Jensen

/-- **Cor. `corol:lpInclusLq` (Injection `L^p`).** Soit `(X, μ)` un espace mesuré de mesure
finie non nulle, et `p ≤ q`. Alors `L^q(X, μ) ⊂ L^p(X, μ)` et pour toute `f ∈ L^q`,
`μ(X)^{-1/p} ‖f‖_p ≤ μ(X)^{-1/q} ‖f‖_q` (avec la convention `1/∞ = 0`).
Remarque : l'hypothèse `1 ≤ p` du cours est superflue.
Preuve (différente du cours) : inégalité de Hölder de Mathlib
(`eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) au lieu de l'inégalité de Jensen. -/
theorem corol_lpInclusLq {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NeZero μ] {E : Type*} [NormedAddCommGroup E] {p q : ℝ≥0∞} (hpq : p ≤ q) {f : X → E}
    (hf : MemLp f q μ) :
    MemLp f p μ ∧
      μ univ ^ (-(1 / p.toReal)) * eLpNorm f p μ ≤ μ univ ^ (-(1 / q.toReal)) * eLpNorm f q μ := by
  refine ⟨hf.mono_exponent hpq, ?_⟩
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf.aestronglyMeasurable
  have h0 : μ univ ≠ 0 := (Measure.measure_univ_pos.2 (NeZero.ne μ)).ne'
  have htop : μ univ ≠ ∞ := measure_ne_top μ univ
  calc μ univ ^ (-(1 / p.toReal)) * eLpNorm f p μ
      ≤ μ univ ^ (-(1 / p.toReal)) *
          (eLpNorm f q μ * μ univ ^ (1 / p.toReal - 1 / q.toReal)) := by gcongr
    _ = eLpNorm f q μ * μ univ ^ (-(1 / p.toReal) + (1 / p.toReal - 1 / q.toReal)) := by
        rw [ENNReal.rpow_add _ _ h0 htop]; ring
    _ = μ univ ^ (-(1 / q.toReal)) * eLpNorm f q μ := by
        rw [mul_comm]; congr 2; ring

/-! ### Convolution dans `L^p` -/

/-- Inégalité de Jensen (ou de Hölder) pour l'intégrale de Lebesgue, sous la forme utilisée
dans la preuve de `prop:convolLp` : pour `p ≥ 1` et `a, b ≥ 0`,
`(∫ a b)^p ≤ (∫ a)^{p-1} ∫ a b^p`. -/
theorem lintegral_mul_rpow_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {p : ℝ}
    (hp : 1 ≤ p) {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    (∫⁻ x, a x * b x ∂μ) ^ p ≤ (∫⁻ x, a x ∂μ) ^ (p - 1) * ∫⁻ x, a x * b x ^ p ∂μ := by
  rcases hp.eq_or_lt with rfl | hp1
  · simp
  have hp0 : 0 < p := zero_lt_one.trans hp1
  set q := p.conjExponent with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq0 : 0 < q := hpq.symm.pos
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (f := fun x => a x ^ (1 / p) * b x) (g := fun x => a x ^ (1 / q))
    ((ha.pow_const _).mul hb) (ha.pow_const _)
  have e1 : ∀ x, (fun x => a x ^ (1 / p) * b x) x * (fun x => a x ^ (1 / q)) x = a x * b x := by
    intro x
    simp only
    rw [mul_comm, ← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
      one_div, one_div, add_comm, hpq.inv_add_inv_eq_one, ENNReal.rpow_one]
  have e2 : ∀ x, (a x ^ (1 / p) * b x) ^ p = a x * b x ^ p := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne',
      ENNReal.rpow_one]
  have e3 : ∀ x, (a x ^ (1 / q)) ^ q = a x := by
    intro x
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, e1, e2, e3] at key
  calc (∫⁻ x, a x * b x ∂μ) ^ p
      ≤ ((∫⁻ x, a x * b x ^ p ∂μ) ^ (1 / p) * (∫⁻ x, a x ∂μ) ^ (1 / q)) ^ p :=
        ENNReal.rpow_le_rpow key hp0.le
    _ = (∫⁻ x, a x ∂μ) ^ (p - 1) * ∫⁻ x, a x * b x ^ p ∂μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          one_div_mul_cancel hp0.ne', ENNReal.rpow_one, mul_comm]
        congr 2
        have h1 : p - 1 ≠ 0 := by linarith
        rw [hq, Real.conjExponent]
        field_simp

section ConvolLp

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Estimation clé de la preuve de `prop:convolLp` : pour `p ≥ 1`,
`∫ (∫ |f(h)| |g(x-h)| dh)^p dx ≤ (∫ |f|)^p ∫ |g|^p`. -/
theorem lintegral_convolution_rpow_le {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] {p : ℝ} (hp : 1 ≤ p) {f : ℝᵈ → E} {g : ℝᵈ → F}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ) ^ p ≤ (∫⁻ t, ‖f t‖ₑ) ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hK : AEMeasurable (fun z : ℝᵈ × ℝᵈ => ‖f z.2‖ₑ * ‖g (z.1 - z.2)‖ₑ ^ p)
      (volume.prod volume) :=
    hf.enorm.comp_snd.mul ((hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).enorm.pow_const p)
  calc ∫⁻ x, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ) ^ p
      ≤ ∫⁻ x, (∫⁻ t, ‖f t‖ₑ) ^ (p - 1) * ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ p :=
        lintegral_mono fun x => lintegral_mul_rpow_le volume hp hf.enorm
          (hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).enorm
    _ = (∫⁻ t, ‖f t‖ₑ) ^ (p - 1) * ∫⁻ x, ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ p :=
        lintegral_const_mul'' _ hK.lintegral_prod_right'
    _ = (∫⁻ t, ‖f t‖ₑ) ^ (p - 1) * ∫⁻ t, ∫⁻ x, ‖f t‖ₑ * ‖g (x - t)‖ₑ ^ p := by
        rw [lintegral_lintegral_swap hK]
    _ = (∫⁻ t, ‖f t‖ₑ) ^ (p - 1) * ∫⁻ t, ‖f t‖ₑ * ∫⁻ x, ‖g x‖ₑ ^ p := by
        congr 1
        refine lintegral_congr fun t => ?_
        have h : AEMeasurable (fun x => ‖g (x - t)‖ₑ ^ p) volume :=
          (hg.comp_measurePreserving (measurePreserving_sub_right volume t)).enorm.pow_const p
        rw [lintegral_const_mul'' _ h]
        rw [lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ ^ p) t]
    _ = (∫⁻ t, ‖f t‖ₑ) ^ p * ∫⁻ x, ‖g x‖ₑ ^ p := by
        rw [lintegral_mul_const'' _ hf.enorm, ← mul_assoc]
        congr 1
        conv_rhs => rw [show p = (p - 1) + 1 by ring]
        rw [ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one, ENNReal.rpow_one]

/-- Norme de `lsmul ℝ ℝ` (le produit) : `‖lsmul‖ₑ ≤ 1`. -/
theorem enorm_lsmul_le : ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ ≤ 1 := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_one.2 (ContinuousLinearMap.opNorm_lsmul_le)

/-- Si `∫ |f(h)| |g(x - h)| dh < ∞`, alors l'intégrale de convolution converge en `x`. -/
theorem convolutionExistsAt_of_lintegral_lt_top {f g : ℝᵈ → ℝ}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) {x : ℝᵈ}
    (hx : ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ < ∞) : ConvolutionExistsAt f g x (lsmul ℝ ℝ) volume := by
  refine ⟨?_, ?_⟩
  · simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact hf.mul (hg.comp_measurePreserving (Measure.measurePreserving_sub_left volume x))
  · simpa [HasFiniteIntegral, enorm_mul] using hx

/-- Majoration ponctuelle `|f ⋆ g|(x) ≤ ∫ |f(h)| |g(x - h)| dh`. -/
theorem enorm_convolution_le_lintegral (f g : ℝᵈ → ℝ) (x : ℝᵈ) :
    ‖(f ⋆ g) x‖ₑ ≤ ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ := by
  rw [convolution_def]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  simp [enorm_mul]

/-- **Prop. `prop:convolLp` (Convolution dans `L^p`).** Soient `f ∈ L^1(ℝ^d)` et
`g ∈ L^p(ℝ^d)`, `p ∈ [1, ∞]`. Alors l'intégrale `(f ⋆ g)(x) = ∫ f(h) g(x - h) dh` converge pour
presque tout `x`, `f ⋆ g ∈ L^p` et `‖f ⋆ g‖_p ≤ ‖f‖_1 ‖g‖_p`. -/
theorem prop_convolLp {p : ℝ≥0∞} (hp : 1 ≤ p) {f g : ℝᵈ → ℝ} (hf : Integrable f)
    (hg : MemLp g p) :
    (∀ᵐ x, ConvolutionExistsAt f g x (lsmul ℝ ℝ) volume) ∧ MemLp (f ⋆ g) p ∧
      eLpNorm (f ⋆ g) p ≤ eLpNorm f 1 * eLpNorm g p := by
  have hfg : AEStronglyMeasurable (f ⋆ g) volume :=
    hf.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hg.aestronglyMeasurable
  have hf1 : MemLp f 1 := memLp_one_iff_integrable.2 hf
  suffices H : (∀ᵐ x, ConvolutionExistsAt f g x (lsmul ℝ ℝ) volume) ∧
      eLpNorm (f ⋆ g) p ≤ eLpNorm f 1 * eLpNorm g p from
    ⟨H.1, H.2.trans_lt (ENNReal.mul_lt_top hf1.eLpNorm_lt_top hg.eLpNorm_lt_top), H.2⟩
  rcases eq_or_ne p ∞ with rfl | hpt
  · refine ⟨ae_of_all _ (ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ) hf1 hg), ?_⟩
    rw [eLpNorm_exponent_top hfg]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
    refine (enorm_convolution_le (lsmul ℝ ℝ) (p := 1) (q := ∞) hf.aestronglyMeasurable
      hg.aestronglyMeasurable x).trans ?_
    rw [mul_assoc]
    exact mul_le_of_le_one_left' enorm_lsmul_le
  set r := p.toReal with hr_def
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ r := by
    rw [hr_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  set F : ℝᵈ → ℝ≥0∞ := fun x => ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ with hF_def
  have hFm : AEMeasurable F volume :=
    (hf.aestronglyMeasurable.enorm.comp_snd.mul (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).enorm).lintegral_prod_right'
  have hgE : ∫⁻ x, ‖g x‖ₑ ^ r = eLpNorm g p ^ r := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hg.aestronglyMeasurable, ← hr_def,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
  have hfE : ∫⁻ t, ‖f t‖ₑ = eLpNorm f 1 :=
    (eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm
  have key : ∫⁻ x, F x ^ r ≤ (eLpNorm f 1 * eLpNorm g p) ^ r := by
    refine (lintegral_convolution_rpow_le hr hf.aestronglyMeasurable
      hg.aestronglyMeasurable).trans (le_of_eq ?_)
    rw [hgE, hfE, ENNReal.mul_rpow_of_nonneg _ _ hr0.le]
  have hfin : ∫⁻ x, F x ^ r ≠ ∞ :=
    (key.trans_lt (ENNReal.rpow_lt_top_of_nonneg hr0.le
      (ENNReal.mul_lt_top hf1.eLpNorm_lt_top hg.eLpNorm_lt_top).ne)).ne
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_lt_top' (hFm.pow_const r) hfin] with x hx
    exact convolutionExistsAt_of_lintegral_lt_top hf.aestronglyMeasurable
      hg.aestronglyMeasurable ((ENNReal.rpow_lt_top_iff_of_pos hr0).1 hx)
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hfg, ← hr_def]
    have h1 : (∫⁻ x, ‖(f ⋆ g) x‖ₑ ^ r) ^ (1 / r) ≤ (∫⁻ x, F x ^ r) ^ (1 / r) := by
      gcongr with x
      exact enorm_convolution_le_lintegral f g x
    refine h1.trans ((ENNReal.rpow_le_rpow key (by positivity)).trans (le_of_eq ?_))
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hr0.ne', ENNReal.rpow_one]

open scoped Pointwise in
/-- **Éq. `eq:suppConvol` (Support d'une convolution).** `supp(f ⋆ g) ⊂ adh(supp f + supp g)`.
Encodage : `f, g : ℝ^d → ℝ` sont des fonctions (et non des classes), `supp` est le support
topologique `tsupport` (adhérence de `{f ≠ 0}`), et `f ⋆ g` est la convolution
`x ↦ ∫ f(h) g(x - h) dh` (valant `0` là où l'intégrale n'existe pas). L'inclusion vaut sans
hypothèse d'intégrabilité, pour tout représentant de `f` et `g` ; comme `f ⋆ g` ne dépend que
des classes de `f` et `g`, elle implique la version pour les supports essentiels des classes
`f ∈ L^1`, `g ∈ L^p` du cours. -/
theorem eq_suppConvol (f g : ℝᵈ → ℝ) :
    tsupport (f ⋆ g) ⊆ closure (tsupport f + tsupport g) :=
  closure_mono (Subset.trans (support_convolution_subset (lsmul ℝ ℝ))
    (add_subset_add (subset_tsupport f) (subset_tsupport g)))

/-- **Lemme `lem:convolTranslat` (Convolution et translation).** Soit `f ∈ L^1(ℝ^d, ℝ_+)`
d'intégrale unité, `g ∈ L^p(ℝ^d)` (`1 ≤ p < ∞`) et `A ⊆ ℝ^d` mesurable. Alors
`‖f ⋆ g - g‖^p_{L^p(A)} ≤ ∫ f(h) ‖τ_h g - g‖^p_{L^p(A)} dh`, où `τ_h g(x) = g(x - h)`.
(Le membre de droite est une intégrale de Lebesgue de fonction positive, `∫⁻`.)
Remarque : l'hypothèse « `A` mesurable » est superflue. -/
theorem lem_convolTranslat {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f g : ℝᵈ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) (hf1 : ∫ x, f x = 1) (hg : MemLp g p)
    (A : Set ℝᵈ) :
    eLpNorm (f ⋆ g - g) p (volume.restrict A) ^ p.toReal ≤
      ∫⁻ h, ENNReal.ofReal (f h) *
        eLpNorm (fun x => g (x - h) - g x) p (volume.restrict A) ^ p.toReal := by
  set r := p.toReal with hr_def
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ r := by
    rw [hr_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hgm := hg.aestronglyMeasurable
  have hfg : AEStronglyMeasurable (f ⋆ g) volume :=
    hf.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hgm
  have hτ : ∀ h, AEStronglyMeasurable (fun x => g (x - h) - g x) volume := fun h =>
    (hgm.comp_measurePreserving (measurePreserving_sub_right volume h)).sub hgm
  -- expression des deux membres par des intégrales de Lebesgue
  have hL : eLpNorm (f ⋆ g - g) p (volume.restrict A) ^ r =
      ∫⁻ x in A, ‖(f ⋆ g) x - g x‖ₑ ^ r := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hfg.sub hgm).restrict, ← hr_def,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
    rfl
  have hR : ∀ h, eLpNorm (fun x => g (x - h) - g x) p (volume.restrict A) ^ r =
      ∫⁻ x in A, ‖g (x - h) - g x‖ₑ ^ r := by
    intro h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hτ h).restrict, ← hr_def,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
  simp_rw [hL, hR]
  have hfint : ∫⁻ h, ENNReal.ofReal (f h) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hf0), hf1, ENNReal.ofReal_one]
  -- majoration ponctuelle (Jensen)
  have hpt_bound : ∀ᵐ x, ‖(f ⋆ g) x - g x‖ₑ ^ r ≤
      ∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ ^ r := by
    filter_upwards [(prop_convolLp hp hf hg).1] with x hx
    have hint : Integrable (fun h => f h * g (x - h)) := by
      simpa [ConvolutionExistsAt] using hx
    have heq : (f ⋆ g) x - g x = ∫ h, f h * (g (x - h) - g x) := by
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]
      rw [integral_sub hint (hf.mul_const _), integral_mul_const, hf1, one_mul]
    have h1 : ‖(f ⋆ g) x - g x‖ₑ ≤ ∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ := by
      rw [heq]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp [enorm_mul, Real.enorm_of_nonneg (hf0 _)]
    calc ‖(f ⋆ g) x - g x‖ₑ ^ r
        ≤ (∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ) ^ r := by gcongr
      _ ≤ (∫⁻ h, ENNReal.ofReal (f h)) ^ (r - 1) *
            ∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ ^ r :=
          lintegral_mul_rpow_le volume hr hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
            ((hgm.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).sub
              aestronglyMeasurable_const).enorm
      _ = ∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ ^ r := by
          rw [hfint, ENNReal.one_rpow, one_mul]
  -- intégration sur `A` et Fubini–Tonelli
  have hK : AEMeasurable (fun z : ℝᵈ × ℝᵈ => ENNReal.ofReal (f z.2) * ‖g (z.1 - z.2) - g z.1‖ₑ ^ r)
      ((volume.restrict A).prod volume) := by
    refine AEMeasurable.mono_ac ?_ (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
      Measure.AbsolutelyContinuous.rfl)
    exact hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_snd.mul
      (((hgm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant
        volume volume)).sub hgm.aemeasurable.comp_fst.aestronglyMeasurable).enorm.pow_const r)
  calc ∫⁻ x in A, ‖(f ⋆ g) x - g x‖ₑ ^ r
      ≤ ∫⁻ x in A, ∫⁻ h, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ ^ r :=
        lintegral_mono_ae (ae_restrict_of_ae hpt_bound)
    _ = ∫⁻ h, ∫⁻ x in A, ENNReal.ofReal (f h) * ‖g (x - h) - g x‖ₑ ^ r :=
        lintegral_lintegral_swap hK
    _ = ∫⁻ h, ENNReal.ofReal (f h) * ∫⁻ x in A, ‖g (x - h) - g x‖ₑ ^ r := by
        refine lintegral_congr fun h => ?_
        exact lintegral_const_mul'' _ ((hτ h).enorm.pow_const r).restrict

/-! ### Dérivation d'une convolution -/

/-- Différentielles itérées d'une convolution : si `f ∈ L^1` et `g ∈ C^k_c`, alors pour
`m ≤ k`, `D^m (f ⋆ g) = f ⋆ D^m g`. -/
theorem iteratedFDeriv_convolution {k : ℕ} {f g : ℝᵈ → ℝ} (hf : Integrable f)
    (hg : ContDiff ℝ k g) (hgc : HasCompactSupport g) {m : ℕ} (hm : m ≤ k) :
    iteratedFDeriv ℝ m (f ⋆ g) = f ⋆[lsmul ℝ ℝ] iteratedFDeriv ℝ m g := by
  induction m with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
    funext x
    simp only [Function.comp_apply, convolution_def]
    rw [← LinearIsometryEquiv.coe_toLinearIsometry, ← LinearIsometry.integral_comp_comm]
    congr 1
  | succ m ih =>
    have hm' : m ≤ k := by omega
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih hm']
    funext x
    have hGm : ContDiff ℝ 1 (iteratedFDeriv ℝ m g) :=
      hg.iteratedFDeriv_right (by exact_mod_cast (by omega : 1 + m ≤ k))
    have hGc : HasCompactSupport (iteratedFDeriv ℝ m g) := hgc.iteratedFDeriv m
    simp only [Function.comp_apply]
    rw [(hGc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable hGm x).fderiv]
    simp only [convolution_def]
    rw [← LinearIsometryEquiv.coe_toLinearIsometry, ← LinearIsometry.integral_comp_comm]
    congr 1

/-- **Prop. `prop:convolDeriv` (Dérivation d'une convolution).** Soit `f ∈ L^1(ℝ^d)` et
`g ∈ C^k_c(ℝ^d)`. Alors `f ⋆ g ∈ C^k(ℝ^d)` et `∂_α (f ⋆ g) = f ⋆ (∂_α g)` pour `|α|_1 ≤ k`
(`deriveePartielle`, cf. `def:normeCnb`) ; voir aussi `iteratedFDeriv_convolution` pour la
version intrinsèque `D^j (f ⋆ g) = f ⋆ D^j g`.
Preuve (différente du cours) : régularité et différentielle de `f ⋆ g` fournies par Mathlib
(`HasCompactSupport.contDiff_convolution_right`, `hasFDerivAt_convolution_right`), par
dérivation sous l'intégrale (convergence dominée, `Dg` bornée), sans taux d'accroissement. -/
theorem prop_convolDeriv {k : ℕ} {f g : ℝᵈ → ℝ} (hf : Integrable f) (hg : ContDiff ℝ k g)
    (hgc : HasCompactSupport g) :
    ContDiff ℝ k (f ⋆ g) ∧
      ∀ α : Fin d → ℕ, ∑ i, α i ≤ k → deriveePartielle α (f ⋆ g) = f ⋆ deriveePartielle α g := by
  refine ⟨hgc.contDiff_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable hg,
    fun α hα => ?_⟩
  have hj : (directions α).length ≤ k := (length_directions α).trans_le hα
  funext x
  simp only [deriveePartielle]
  rw [iteratedFDeriv_convolution hf hg hgc hj]
  simp only [convolution_def]
  have hint : Integrable (fun t => lsmul ℝ ℝ (f t)
      (iteratedFDeriv ℝ (directions α).length g (x - t))) :=
    (hgc.iteratedFDeriv _).convolutionExists_right (lsmul ℝ ℝ) hf.locallyIntegrable
      (hg.continuous_iteratedFDeriv (by exact_mod_cast hj)) x
  rw [ContinuousMultilinearMap.integral_apply hint]
  simp [deriveePartielle]

/-! ### Densité de `𝓓(Ω)` dans `L^p(Ω)` -/

/-- **Cor. `corol:testDenseLp` (Densité de `𝓓(Ω)` dans `L^p`).** Soit `Ω ⊆ ℝ^d` ouvert et
`1 ≤ p < ∞`. Alors `𝓓(Ω)` est dense dans `L^p(Ω)` : pour toute `f ∈ L^p(Ω)` et tout `ε > 0`, il
existe `φ ∈ 𝓓(Ω)` avec `‖f - φ‖_{L^p(Ω)} ≤ ε`.
Remarque : `L^p(Ω)` est représenté par les fonctions sur `ℝ^d` de puissance `p`-ième intégrable
pour la mesure de Lebesgue restreinte à `Ω`, et `𝓓(Ω)` par `𝓓(Ω, ℝ)` (`TestFunction`). (Preuve :
approximation `C^∞_c(ℝ^d)` de Mathlib, `MemLp.exist_eLpNorm_sub_le`, puis troncature par une
fonction plateau de `prop:cinfSupport`.) -/
theorem corol_testDenseLp (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : ℝᵈ → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set ℝᵈ))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : 𝓓(Ω, ℝ), eLpNorm (f - ⇑φ) p (volume.restrict (Ω : Set ℝᵈ)) ≤ ENNReal.ofReal ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hgc, hgs, hfg⟩ := hf.exist_eLpNorm_sub_le hpt hp hε2
  obtain ⟨M, hM⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  obtain ⟨η, ηpos, hη⟩ := exists_eLpNorm_indicator_le (μ := volume.restrict (Ω : Set ℝᵈ)) hpt M
    (ENNReal.ofReal_pos.2 hε2).ne'
  set S := (Ω : Set ℝᵈ) ∩ tsupport g with hS_def
  have hSm : MeasurableSet S := Ω.isOpen.measurableSet.inter (isClosed_tsupport g).measurableSet
  have hSf : volume S ≠ ∞ := ((measure_mono inter_subset_right).trans_lt hgc.measure_lt_top).ne
  obtain ⟨K, hKS, hK, hSK⟩ := hSm.exists_isCompact_sdiff_lt hSf (ENNReal.coe_pos.2 ηpos).ne'
  obtain ⟨χ, hχ, hχc, hχΩ, hχ01, hχ1⟩ :=
    prop_cinfSupport Ω.isOpen hK (hKS.trans inter_subset_left)
  let φ : 𝓓(Ω, ℝ) := ⟨χ * g, hχ.mul hgs, hχc.mul_right, tsupport_mul_subset_left.trans hχΩ⟩
  refine ⟨φ, ?_⟩
  have hφ : ∀ x, φ x = χ x * g x := fun _ => rfl
  have hbound : ∀ x, ‖(g - ⇑φ) x‖ ≤ ‖(tsupport g \ K).indicator (fun _ => M) x‖ := by
    intro x
    rw [Pi.sub_apply, hφ, show g x - χ x * g x = (1 - χ x) * g x by ring]
    by_cases hx : x ∈ tsupport g \ K
    · rw [indicator_of_mem hx, norm_mul]
      have h1 : ‖1 - χ x‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hχ01 x).1, (hχ01 x).2]
      calc ‖1 - χ x‖ * ‖g x‖ ≤ 1 * M := mul_le_mul h1 (hM x) (norm_nonneg _) zero_le_one
        _ ≤ ‖M‖ := by rw [one_mul]; exact Real.le_norm_self M
    · rw [indicator_of_notMem hx, norm_zero]
      rcases not_and_or.1 hx with hx | hx
      · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, norm_zero]
      · rw [not_not] at hx
        rw [hχ1 hx, Pi.one_apply, sub_self, zero_mul, norm_zero]
  have hm : MeasurableSet (tsupport g \ K) :=
    (isClosed_tsupport g).measurableSet.diff hK.measurableSet
  have h2 : eLpNorm (g - ⇑φ) p (volume.restrict (Ω : Set ℝᵈ)) ≤ ENNReal.ofReal (ε / 2) := by
    refine (eLpNorm_mono (hgs.continuous.sub φ.continuous).aestronglyMeasurable hbound).trans
      (hη _ ?_ hm.nullMeasurableSet)
    rw [Measure.restrict_apply hm]
    refine (measure_mono ?_).trans hSK.le
    rintro x ⟨⟨hxg, hxK⟩, hxΩ⟩
    exact ⟨⟨hxΩ, hxg⟩, hxK⟩
  calc eLpNorm (f - ⇑φ) p (volume.restrict (Ω : Set ℝᵈ))
      = eLpNorm ((f - g) + (g - ⇑φ)) p (volume.restrict (Ω : Set ℝᵈ)) := by
        rw [sub_add_sub_cancel]
    _ ≤ eLpNorm (f - g) p (volume.restrict (Ω : Set ℝᵈ)) +
          eLpNorm (g - ⇑φ) p (volume.restrict (Ω : Set ℝᵈ)) := eLpNorm_add_le hp
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hfg h2
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]

/-- **Prop. `prop:densC0Lp`, cas d'un ouvert `Ω ⊆ ℝ^d`.** `C^0_c(Ω)` est dense dans
`L^p(Ω)` pour `1 ≤ p < ∞` : pour toute `f ∈ L^p(Ω)` et `ε > 0`, il existe `g` continue à support
compact contenu dans `Ω` avec `‖f - g‖_{L^p(Ω)} ≤ ε`.
Remarque : déduit ici de `corol:testDenseLp` (et non de la régularité de la mesure de Lebesgue
sur `Ω`, comme dans le cours). -/
theorem prop_densC0Lp_ouvert (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : ℝᵈ → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set ℝᵈ))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : ℝᵈ → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ω ∧
      eLpNorm (f - g) p (volume.restrict (Ω : Set ℝᵈ)) ≤ ENNReal.ofReal ε := by
  obtain ⟨φ, hφ⟩ := corol_testDenseLp Ω hp hpt hf hε
  exact ⟨φ, φ.continuous, φ.hasCompactSupport, φ.tsupport_subset, hφ⟩

/-! ### Approximation par convolution -/

/-- Noyau dilaté `ρ_ε(x) = ε^{-d} ρ(x / ε)` du cours. -/
noncomputable def noyauEps (ρ : ℝᵈ → ℝ) (ε : ℝ) : ℝᵈ → ℝ :=
  fun x => (ε ^ d)⁻¹ * ρ (ε⁻¹ • x)

/-- Module de continuité sous translation `ω_p(ε) = sup_{|h| ≤ ε} ‖f - τ_h f‖_p`, où
`τ_h f(x) = f(x - h)`. -/
noncomputable def moduleTransl (p : ℝ≥0∞) (f : ℝᵈ → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨆ h ∈ closedBall (0 : ℝᵈ) ε, eLpNorm (fun x => f x - f (x - h)) p volume

theorem noyauEps_nonneg {ρ : ℝᵈ → ℝ} {ε : ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hε : 0 < ε) (x : ℝᵈ) :
    0 ≤ noyauEps ρ ε x :=
  mul_nonneg (inv_nonneg.2 (pow_nonneg hε.le d)) (hρ0 _)

theorem integrable_noyauEps {ρ : ℝᵈ → ℝ} {ε : ℝ} (hρ : Integrable ρ) (hε : 0 < ε) :
    Integrable (noyauEps ρ ε) :=
  (hρ.comp_smul (inv_ne_zero hε.ne')).const_mul _

theorem integral_noyauEps {ρ : ℝᵈ → ℝ} {ε : ℝ} (hε : 0 < ε) : ∫ x, noyauEps ρ ε x = ∫ x, ρ x := by
  simp only [noyauEps]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume ρ hε.le,
    finrank_euclideanSpace_fin, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero d hε.ne'), one_mul]

theorem norm_le_of_noyauEps_ne_zero {ρ : ℝᵈ → ℝ} {ε : ℝ}
    (hρs : Function.support ρ ⊆ closedBall 0 1) (hε : 0 < ε)
    {x : ℝᵈ} (hx : noyauEps ρ ε x ≠ 0) : ‖x‖ ≤ ε := by
  have h1 : ρ (ε⁻¹ • x) ≠ 0 := fun h => hx (by simp [noyauEps, h])
  have h2 := hρs h1
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le),
    inv_mul_le_iff₀ hε, mul_one] at h2
  exact h2

/-- **Prop. `prop:convolApprox` (Approximation par convolution), cas `p < ∞`, estimation.**
Soit `ρ ∈ L^1(ℝ^d, ℝ_+)` supportée dans `B'(0, 1)` et d'intégrale unité, `p ∈ [1, ∞[` et
`f ∈ L^p(ℝ^d)`. Alors `‖f - ρ_ε ⋆ f‖_p ≤ ω_p(ε)` pour tout `ε > 0`. -/
theorem prop_convolApprox_le {ρ : ℝᵈ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ)
    (hρs : Function.support ρ ⊆ closedBall 0 1) (hρ1 : ∫ x, ρ x = 1) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : ℝᵈ → ℝ} (hf : MemLp f p) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (f - noyauEps ρ ε ⋆ f) p ≤ moduleTransl p f ε := by
  set r := p.toReal with hr_def
  have hr0 : 0 < r := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpt
  have hint := integrable_noyauEps hρ hε
  have H := lem_convolTranslat hp hpt (noyauEps_nonneg hρ0 hε) hint
    ((integral_noyauEps hε).trans hρ1) hf univ
  simp only [Measure.restrict_univ] at H
  have hfint : ∫⁻ h, ENNReal.ofReal (noyauEps ρ ε h) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (noyauEps_nonneg hρ0 hε)),
      integral_noyauEps hε, hρ1, ENNReal.ofReal_one]
  have H2 : ∫⁻ h, ENNReal.ofReal (noyauEps ρ ε h) *
        eLpNorm (fun x => f (x - h) - f x) p volume ^ r ≤
      ∫⁻ h, ENNReal.ofReal (noyauEps ρ ε h) * moduleTransl p f ε ^ r := by
    refine lintegral_mono fun h => ?_
    by_cases hh : noyauEps ρ ε h = 0
    · simp [hh]
    · gcongr
      have he : eLpNorm (fun x => f (x - h) - f x) p volume =
          eLpNorm (fun x => f x - f (x - h)) p volume := by
        rw [← eLpNorm_neg]
        congr 1
        funext x
        simp
      rw [he]
      exact le_iSup₂ (f := fun h (_ : h ∈ closedBall (0 : ℝᵈ) ε) =>
        eLpNorm (fun x => f x - f (x - h)) p volume) h
        (mem_closedBall_zero_iff.2 (norm_le_of_noyauEps_ne_zero hρs hε hh))
  rw [lintegral_mul_const'' _ hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal, hfint,
    one_mul] at H2
  rw [eLpNorm_sub_comm]
  exact (ENNReal.rpow_le_rpow_iff hr0).1 (H.trans H2)

/-- **Prop. `prop:convolApprox` (Approximation par convolution), cas `p < ∞`, convergence.**
Pour `f ∈ L^p(ℝ^d)`, `p ∈ [1, ∞[`, on a `ω_p(ε) → 0` lorsque `ε → 0⁺` (continuité des
translations dans `L^p`, par densité des fonctions continues à support compact). -/
theorem prop_convolApprox_tendsto {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : ℝᵈ → ℝ}
    (hf : MemLp f p) : Tendsto (moduleTransl p f) (𝓝[>] 0) (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set r := p.toReal with hr_def
  have hr0 : 0 < r := ENNReal.toReal_pos hp0 hpt
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  obtain ⟨a, -, ha, haη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have ha0 : 0 < a := ENNReal.ofReal_pos.1 ha
  set e := a / 3 with he
  have he0 : 0 < e := by positivity
  obtain ⟨g, hgc, hfg, hgcont, -⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le hpt (ENNReal.ofReal_pos.2 he0).ne'
  set K := cthickening 1 (tsupport g) with hK_def
  have hK : IsCompact K := IsCompact.cthickening hgc
  have hC : volume K ≠ ∞ := hK.measure_lt_top.ne
  set c := (volume K).toReal ^ (1 / r) with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hCc : volume K ^ (1 / r) = ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_toReal hC, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
      (by positivity)]
  set e' := e / (c + 1) with he'_def
  have he'0 : 0 < e' := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
    (hgcont.uniformContinuous_of_tendsto_cocompact hgc.is_zero_at_infty) e' he'0
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ0 zero_lt_one)] with ε hε
  refine (iSup₂_le fun h hh => ?_).trans haη.le
  rw [mem_closedBall_zero_iff] at hh
  have hhδ : ‖h‖ < δ := hh.trans_lt (hε.2.trans_le (min_le_left _ _))
  have hh1 : ‖h‖ ≤ 1 := hh.trans (hε.2.trans_le (min_le_right _ _)).le
  have hmp := measurePreserving_sub_right (volume : Measure ℝᵈ) h
  have hfm := hf.aestronglyMeasurable
  have hgm : AEStronglyMeasurable g volume := hgcont.aestronglyMeasurable
  have T3 : eLpNorm (fun x => g (x - h) - f (x - h)) p ≤ ENNReal.ofReal e := by
    have : (fun x => g (x - h) - f (x - h)) = (g - f) ∘ (fun x => x - h) := rfl
    rw [this, eLpNorm_comp_measurePreserving (hgm.sub hfm) hmp, eLpNorm_sub_comm]
    exact hfg
  have T2 : eLpNorm (fun x => g x - g (x - h)) p ≤ ENNReal.ofReal e := by
    have hdist : ∀ x : ℝᵈ, dist x (x - h) = ‖h‖ := fun x => by
      rw [dist_eq_norm, sub_sub_cancel]
    have H := eLpNorm_sub_le_of_dist_bdd volume hpt hK.measurableSet.nullMeasurableSet he'0.le
      (f := g) (g := fun x => g (x - h))
      (hgcont.sub (hgcont.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
      (fun x => (hδ (by rw [hdist]; exact hhδ)).le)
      ((subset_tsupport g).trans (self_subset_cthickening _))
      (fun x hx => mem_cthickening_of_dist_le x (x - h) 1 _ (subset_tsupport g hx)
        (by rw [hdist]; exact hh1))
    refine H.trans ?_
    rw [hCc, ← ENNReal.ofReal_mul he'0.le]
    apply ENNReal.ofReal_le_ofReal
    rw [he'_def, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    exact mul_le_mul_of_nonneg_left (by linarith) he0.le
  have hdec : (fun x => f x - f (x - h)) = (fun x => f x - g x) + (fun x => g x - g (x - h)) +
      (fun x => g (x - h) - f (x - h)) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have T1 : eLpNorm (fun x => f x - g x) p ≤ ENNReal.ofReal e := hfg
  have hsum : ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal e = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_add he0.le he0.le, ← ENNReal.ofReal_add (by positivity) he0.le, he]
    congr 1
    ring
  rw [hdec, ← hsum]
  refine (eLpNorm_add_le hp).trans (add_le_add ((eLpNorm_add_le hp).trans
    (add_le_add T1 T2)) T3)

/-- Pour `u` continue, `|u(x)| ≤ ‖u‖_∞` en tout point (la mesure de Lebesgue charge les
ouverts). -/
theorem enorm_le_eLpNorm_top_of_continuous {u : ℝᵈ → ℝ} (hu : Continuous u) (x : ℝᵈ) :
    ‖u x‖ₑ ≤ eLpNorm u ∞ := by
  rw [eLpNorm_exponent_top hu.aestronglyMeasurable]
  by_contra hlt
  rw [not_le] at hlt
  set U := {y | eLpNormEssSup u volume < ‖u y‖ₑ} with hU_def
  have hU : IsOpen U := isOpen_lt continuous_const hu.enorm
  have h0 : volume U = 0 := by
    have := ae_le_eLpNormEssSup (μ := volume) (f := u)
    rw [ae_iff] at this
    simpa [hU_def, not_le] using this
  have hUe : U = ∅ := (hU.measure_eq_zero_iff volume).1 h0
  have hxU : x ∈ U := hlt
  rw [hUe] at hxU
  exact hxU

/-- **Prop. `prop:convolApprox` (Approximation par convolution), cas `p = ∞`.**
Soit `ρ ∈ L^1(ℝ^d, ℝ_+)` supportée dans `B'(0, 1)` et d'intégrale unité, et `f ∈ C^0_0(ℝ^d)`
(continue, tendant vers `0` à l'infini). Alors `‖f - ρ_ε ⋆ f‖_∞ ≤ ω_∞(ε)` pour tout `ε > 0`,
et `ω_∞(ε) → 0` lorsque `ε → 0⁺`. -/
theorem prop_convolApprox_top {ρ : ℝᵈ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ)
    (hρs : Function.support ρ ⊆ closedBall 0 1) (hρ1 : ∫ x, ρ x = 1) {f : ℝᵈ → ℝ}
    (hfc : Continuous f) (hf0 : Tendsto f (cocompact ℝᵈ) (𝓝 0)) :
    (∀ ε > 0, eLpNorm (f - noyauEps ρ ε ⋆ f) ∞ ≤ moduleTransl ∞ f ε) ∧
      Tendsto (moduleTransl ∞ f) (𝓝[>] 0) (𝓝 0) := by
  have hτ : ∀ h : ℝᵈ, Continuous fun x => f x - f (x - h) := fun h =>
    hfc.sub (hfc.comp (continuous_id.sub continuous_const))
  refine ⟨fun ε hε => ?_, ?_⟩
  · obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖f x‖ ≤ C := by
      let F : ZeroAtInftyContinuousMap ℝᵈ ℝ := ⟨⟨f, hfc⟩, hf0⟩
      exact ⟨‖F.toBCF‖, fun x => F.toBCF.norm_coe_le_norm x⟩
    have hint := integrable_noyauEps hρ hε
    have hfint : ∫⁻ h, ENNReal.ofReal (noyauEps ρ ε h) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (noyauEps_nonneg hρ0 hε)),
        integral_noyauEps hε, hρ1, ENNReal.ofReal_one]
    rw [eLpNorm_exponent_top (hfc.aestronglyMeasurable.sub
      (hint.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hfc.aestronglyMeasurable))]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
    have hconv : Integrable (fun h => noyauEps ρ ε h * f (x - h)) :=
      hint.mul_bdd (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (ae_of_all _ fun h => hC _)
    have heq : (f - noyauEps ρ ε ⋆ f) x = ∫ h, noyauEps ρ ε h * (f x - f (x - h)) := by
      rw [Pi.sub_apply, convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]
      rw [integral_sub (hint.mul_const _) hconv, integral_mul_const, integral_noyauEps hε, hρ1,
        one_mul]
    rw [heq]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    calc ∫⁻ h, ‖noyauEps ρ ε h * (f x - f (x - h))‖ₑ
        ≤ ∫⁻ h, ENNReal.ofReal (noyauEps ρ ε h) * moduleTransl ∞ f ε := by
          refine lintegral_mono fun h => ?_
          rw [enorm_mul, Real.enorm_of_nonneg (noyauEps_nonneg hρ0 hε h)]
          by_cases hh : noyauEps ρ ε h = 0
          · simp [hh]
          · gcongr
            exact (enorm_le_eLpNorm_top_of_continuous (hτ h) x).trans
              (le_iSup₂ (f := fun h (_ : h ∈ closedBall (0 : ℝᵈ) ε) =>
                eLpNorm (fun x => f x - f (x - h)) ∞ volume) h
                (mem_closedBall_zero_iff.2 (norm_le_of_noyauEps_ne_zero hρs hε hh)))
      _ = moduleTransl ∞ f ε := by
          rw [lintegral_mul_const'' _ hint.aestronglyMeasurable.aemeasurable.ennreal_ofReal,
            hfint, one_mul]
  · rw [ENNReal.tendsto_nhds_zero]
    intro η hη
    obtain ⟨a, -, ha, haη⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    have ha0 : 0 < a := ENNReal.ofReal_pos.1 ha
    obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.1
      (hfc.uniformContinuous_of_tendsto_cocompact hf0) a ha0
    filter_upwards [Ioo_mem_nhdsGT hδ0] with ε hε
    refine (iSup₂_le fun h hh => ?_).trans haη.le
    rw [mem_closedBall_zero_iff] at hh
    rw [eLpNorm_exponent_top (hτ h).aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
    have hd : dist x (x - h) < δ := by
      rw [dist_eq_norm, sub_sub_cancel]
      exact hh.trans_lt hε.2
    rw [← ofReal_norm, ← dist_eq_norm]
    exact ENNReal.ofReal_le_ofReal (hδ hd).le

end ConvolLp

end M1Analyse
