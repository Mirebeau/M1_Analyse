/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.InjSousCritique
import M1Analyse.Sobolev.NoyauGreen
import M1Analyse.Sobolev.W1p

/-!
# §5.3 Injection de Sobolev sous-critique dans `W^{1,p}` (`subsec:injSousCrit`, suite)

Source : `Include/Sobolev.tex`, `th:injSousCrit` et `corol:injSousCritOm`.

Décision de l'auteur : seul le cas `s = 1`, `p > 1` est formalisé (le cas `p = 1`, dû à
Gagliardo–Nirenberg, n'est pas démontré dans le cours). Les espaces `W^{1,p}` sont ceux de
`M1Analyse/Sobolev/W1p.lean`. Ces résultats dépendent de l'axiome de Young faible.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

local notation "𝕋" => (⊤ : TopologicalSpace.Opens ℝᵈ)

private lemma injSousCrit_abs_le (L : ℝᵈ →L[ℝ] ℝ) (y : ℝᵈ) :
    |L y| ≤ (∑ i, |L (EuclideanSpace.single i 1)|) * ‖y‖ := by
  have hy : y = ∑ i, y i • EuclideanSpace.single i (1:ℝ) := by
    simpa using ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr y).symm
  rw [hy, map_sum, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, smul_eq_mul, abs_mul, mul_comm]
  gcongr
  rw [← hy]
  exact (Real.norm_eq_abs _).symm.le.trans (PiLp.norm_apply_le y i)

/-- Majoration ponctuelle déduite de `prop_convolPow`. -/
private lemma injSousCrit_pointwise (hd : 1 ≤ d) {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : ℝᵈ) :
    ‖f x‖ₑ ≤ ∫⁻ t, ‖(1 / (volume : Measure ℝᵈ).toSphere.real univ) *
        ∑ i, |fderiv ℝ f t (EuclideanSpace.single i 1)|‖ₑ *
      ‖1 / ‖x - t‖ ^ ((d : ℝ) - 1)‖ₑ := by
  set c : ℝ := 1 / (volume : Measure ℝᵈ).toSphere.real univ
  set F : ℝᵈ → ℝ := fun t => ∑ i, |fderiv ℝ f t (EuclideanSpace.single i 1)|
  set g : ℝᵈ → ℝ := fun y => 1 / ‖y‖ ^ ((d : ℝ) - 1)
  have key : ∀ y, ‖inner ℝ (gradient f (x - y)) ((‖y‖ ^ d)⁻¹ • y)‖ₑ ≤
      ‖F (x - y)‖ₑ * ‖g y‖ₑ := by
    intro y
    rw [← enorm_mul]
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [gradient, InnerProductSpace.toDual_symm_apply, map_smul, smul_eq_mul]
    have hF : 0 ≤ F (x - y) := Finset.sum_nonneg fun i _ => abs_nonneg _
    rcases eq_or_ne y 0 with rfl | hy0
    · simp only [map_zero, mul_zero, abs_zero]
      exact abs_nonneg _
    have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hg : g y = (‖y‖ ^ d)⁻¹ * ‖y‖ := by
      simp only [g]
      rw [Real.rpow_sub_one hn.ne', Real.rpow_natCast]
      field_simp
    have hi : 0 < (‖y‖ ^ d)⁻¹ := by positivity
    rw [hg, abs_mul, abs_of_pos hi, abs_of_nonneg (mul_nonneg hF (by positivity))]
    calc (‖y‖ ^ d)⁻¹ * |fderiv ℝ f (x - y) y| ≤ (‖y‖ ^ d)⁻¹ * (F (x - y) * ‖y‖) := by
          gcongr
          exact injSousCrit_abs_le _ _
      _ = _ := by ring
  have h1 : ∫⁻ t, ‖c * F t‖ₑ * ‖g (x - t)‖ₑ = ‖c‖ₑ * ∫⁻ y, ‖F (x - y)‖ₑ * ‖g y‖ₑ := by
    simp_rw [enorm_mul, mul_assoc]
    rw [lintegral_const_mul' _ _ enorm_ne_top]
    congr 1
    rw [← lintegral_sub_left_eq_self (fun y => ‖F (x - y)‖ₑ * ‖g y‖ₑ) x]
    simp
  rw [h1, prop_convolPow hd hf hfc x, enorm_mul]
  gcongr
  exact (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono key)

/-- Exposants réels de `th_injSousCrit`. -/
private lemma injSousCrit_exps {p pstar : ℝ≥0∞} (hp : 1 < p) (hpd : p < d)
    (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹) :
    p = ENNReal.ofReal p.toReal ∧ pstar = ENNReal.ofReal pstar.toReal ∧ 1 < p.toReal ∧
      1 < pstar.toReal ∧ 1 < (d : ℝ) / ((d : ℝ) - 1) ∧ 1 < (d : ℝ) ∧
      1 + 1 / pstar.toReal = 1 / p.toReal + 1 / ((d : ℝ) / ((d : ℝ) - 1)) := by
  have hpt : p ≠ ∞ := (hpd.trans (ENNReal.natCast_lt_top d)).ne
  have hP : 1 < p.toReal := by
    have := ENNReal.toReal_strict_mono hpt hp
    simpa using this
  have hPD : p.toReal < d := by
    have := ENNReal.toReal_strict_mono (ENNReal.natCast_ne_top d) hpd
    simpa using this
  have hD : 1 < (d : ℝ) := hP.trans hPD
  have hlt : (d : ℝ≥0∞)⁻¹ < p⁻¹ := ENNReal.inv_lt_inv.2 hpd
  have hs0 : pstar⁻¹ ≠ 0 := by
    rw [hpstar]; exact (tsub_pos_of_lt hlt).ne'
  have hst : pstar⁻¹ ≠ ∞ := by
    rw [hpstar]
    exact ne_top_of_le_ne_top (ENNReal.inv_ne_top.2 (zero_lt_one.trans hp).ne') tsub_le_self
  have hpst : pstar ≠ ∞ := by simpa using hs0
  have hR : pstar.toReal⁻¹ = p.toReal⁻¹ - (d : ℝ)⁻¹ := by
    rw [← ENNReal.toReal_inv, hpstar, ENNReal.toReal_sub_of_le hlt.le
      (ENNReal.inv_ne_top.2 (zero_lt_one.trans hp).ne'), ENNReal.toReal_inv, ENNReal.toReal_inv]
    simp
  have hR0 : 0 < pstar.toReal := by
    refine ENNReal.toReal_pos ?_ hpst
    intro h; rw [h] at hst; simp at hst
  have hR1 : 1 < pstar.toReal := by
    have h1 : pstar.toReal⁻¹ < 1 := by
      rw [hR]
      have : p.toReal⁻¹ < 1 := inv_lt_one_of_one_lt₀ hP
      have : 0 < (d : ℝ)⁻¹ := by positivity
      linarith
    rwa [inv_lt_one₀ hR0] at h1
  refine ⟨(ENNReal.ofReal_toReal hpt).symm, (ENNReal.ofReal_toReal hpst).symm, hP, hR1, ?_, hD,
    ?_⟩
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · have hD0 : (d : ℝ) - 1 ≠ 0 := by linarith
    rw [one_div, one_div, hR]
    field_simp
    ring

/-- Inégalité de Sobolev pour une fonction `C¹` à support compact. -/
private lemma injSousCrit_test {p pstar : ℝ≥0∞} (hp : 1 < p) (hpd : p < d)
    (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹) :
    ∃ C : ℝ≥0, ∀ f : ℝᵈ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm f pstar ≤ C * ∑ i, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p := by
  obtain ⟨hpe, hse, hP, hR, hq, hD, hpqr⟩ := injSousCrit_exps hp hpd hpstar
  have hd : 1 ≤ d := by exact_mod_cast hD.le
  obtain ⟨C0, hC0⟩ := th_YoungFaible_lintegral (d := d) hP hq hR hpqr
  set c : ℝ := 1 / (volume : Measure ℝᵈ).toSphere.real univ
  set g : ℝᵈ → ℝ := fun y => 1 / ‖y‖ ^ ((d : ℝ) - 1)
  obtain ⟨hgm, hgw⟩ := eq_powLpw (d := d) (α := (d : ℝ) - 1) (by linarith) (by linarith)
  refine ⟨C0 * ‖c‖₊ * (normeFaible volume ((d : ℝ) / ((d : ℝ) - 1)) g).toNNReal,
    fun f hf hfc => ?_⟩
  set F : ℝᵈ → ℝ := fun t => ∑ i, |fderiv ℝ f t (EuclideanSpace.single i 1)|
  have hdf : ∀ i : Fin d, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p := by
    intro i
    exact ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) _)
  have hFm : MemLp (fun t => c * F t) (ENNReal.ofReal p.toReal) := by
    rw [← hpe]
    refine MemLp.const_mul ?_ c
    simp only [F]
    exact memLp_finsetSum _ fun i _ => (hdf i).abs
  have hle := hC0 _ g hFm hgm.aestronglyMeasurable hgw
  have h1 : eLpNorm f pstar ≤
      eLpNorm (fun x => ∫⁻ t, ‖c * F t‖ₑ * ‖g (x - t)‖ₑ) (ENNReal.ofReal pstar.toReal) := by
    rw [← hse]
    refine eLpNorm_mono_enorm hf.continuous.aestronglyMeasurable fun x => ?_
    rw [enorm_eq_self]
    exact injSousCrit_pointwise hd hf hfc x
  have h2 : eLpNorm (fun t => c * F t) (ENNReal.ofReal p.toReal) ≤
      ‖c‖ₑ * ∑ i, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p := by
    rw [← hpe]
    have e1 : (fun t => c * F t) = c • F := rfl
    rw [e1, eLpNorm_const_smul]
    gcongr
    have e2 : F = ∑ i, fun t => |fderiv ℝ f t (EuclideanSpace.single i 1)| := by
      ext t; simp [F]
    rw [e2]
    refine (eLpNorm_sum_le hp.le).trans (Finset.sum_le_sum fun i _ => ?_)
    refine eLpNorm_mono_enorm
      ((hdf i).aestronglyMeasurable.norm.congr (ae_of_all _ fun x => ?_)) fun x => ?_
    · exact Real.norm_eq_abs _
    · simp [Real.enorm_eq_ofReal_abs]
  calc eLpNorm f pstar ≤ _ := h1
    _ ≤ _ := hle
    _ ≤ C0 * (‖c‖ₑ * ∑ i, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p) *
        normeFaible volume ((d : ℝ) / ((d : ℝ) - 1)) g := by gcongr
    _ = ↑(C0 * ‖c‖₊ * (normeFaible volume ((d : ℝ) / ((d : ℝ) - 1)) g).toNNReal) *
        ∑ i, eLpNorm (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) p := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hgw.ne, enorm_eq_nnnorm]
      ring

private lemma injSousCrit_eLpNorm_top {q : ℝ≥0∞} (F : ℝᵈ → ℝ) :
    eLpNorm F q (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)) =
      eLpNorm F q volume := by
  simp

/-- **Th. `th:injSousCrit` (Injection sous-critique `W^{1,p}(ℝ^d) ⊂ L^{p*}(ℝ^d)`), `s = 1`,
`p > 1`.** Soient `p ∈ ]1, d[` et `p*` défini par `1/p* = 1/p - 1/d`. Il existe `C = C(p, d)`
tel que pour tout `u ∈ W^{1,p}(ℝ^d)`, `u ∈ L^{p*}(ℝ^d)` et `‖u‖_{p*} ≤ C ∑ᵢ ‖∂ᵢ u‖_p`.
Remarque : seul le cas `s = 1`, `p > 1` est formalisé (\claudereport) ; le résultat dépend de
l'axiome de Young faible (`th_YoungFaible_lintegral`).
Preuve : celle du cours pour `u ∈ 𝓓(ℝ^d)` (`prop:convolPow`, Young faible, `eq:powLpw`) ; le
passage à `W^{1,p}(ℝ^d)` « par densité » se fait par extraction d'une sous-suite convergeant
presque partout et lemme de Fatou pour la norme `L^{p*}`. -/
theorem th_injSousCrit {p pstar : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hpd : p < d)
    (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹) :
    ∃ C : ℝ≥0, ∀ u : W1p (⊤ : TopologicalSpace.Opens ℝᵈ) p,
      MemLp ((u : LpGrad ⊤ p).fst : ℝᵈ → ℝ) pstar ∧
        eLpNorm ((u : LpGrad ⊤ p).fst : ℝᵈ → ℝ) pstar ≤
          C * ∑ i, eLpNorm ((u : LpGrad ⊤ p).snd i : ℝᵈ → ℝ) p := by
  obtain ⟨C, hC⟩ := injSousCrit_test hp hpd hpstar
  refine ⟨C, fun u => ?_⟩
  have hpt : p ≠ ∞ := (hpd.trans (ENNReal.natCast_lt_top d)).ne
  have hμ : volume.restrict (𝕋 : Set ℝᵈ) = volume := by simp
  have hu : (u : LpGrad 𝕋 p) ∈ closure (SetLike.coe (LinearMap.range (testGrad 𝕋 p))) := by
    rw [← Submodule.topologicalClosure_coe]
    change (u : LpGrad 𝕋 p) ∈ W1p0 𝕋 p
    rw [prop_testDenseWsp_dense hpt]
    exact u.2
  obtain ⟨w, hwr, hw⟩ := mem_closure_iff_seq_limit.1 hu
  choose φ hφ using hwr
  have hfst : Continuous fun x : LpGrad 𝕋 p => x.fst :=
    continuous_fst.comp (WithLp.prod_continuous_ofLp p _ _)
  have hsnd : ∀ i, Continuous fun x : LpGrad 𝕋 p => x.snd i :=
    fun i => (PiLp.continuous_apply p _ i).comp
      (continuous_snd.comp (WithLp.prod_continuous_ofLp p _ _))
  have h1 : Tendsto (fun n => (w n).fst) atTop (𝓝 (u : LpGrad 𝕋 p).fst) :=
    (hfst.tendsto _).comp hw
  have h2 : ∀ i, Tendsto (fun n => eLpNorm ((w n).snd i : ℝᵈ → ℝ) p) atTop
      (𝓝 (eLpNorm ((u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p)) := by
    intro i
    simp_rw [← injSousCrit_eLpNorm_top, ← Lp.enorm_def]
    exact (continuous_enorm.tendsto _).comp (((hsnd i).tendsto _).comp hw)
  have hm : TendstoInMeasure (volume.restrict (𝕋 : Set ℝᵈ))
      (fun n => ((w n).fst : ℝᵈ → ℝ)) atTop ((u : LpGrad 𝕋 p).fst) :=
    tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans hp).ne'
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 h1)
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := pstar)
    (fun k => (Lp.aestronglyMeasurable ((w (ns k)).fst))) _
    (Lp.aestronglyMeasurable (u : LpGrad 𝕋 p).fst) hae
  simp only [injSousCrit_eLpNorm_top] at hfat
  have hk : ∀ k, eLpNorm ((w (ns k)).fst : ℝᵈ → ℝ) pstar ≤
      C * ∑ i, eLpNorm ((w (ns k)).snd i : ℝᵈ → ℝ) p := by
    intro k
    have hae' : ∀ {f g : ℝᵈ → ℝ}, f =ᵐ[volume.restrict (𝕋 : Set ℝᵈ)] g → f =ᵐ[volume] g := by
      intro f g h; rwa [hμ] at h
    rw [← hφ (ns k), eLpNorm_congr_ae (hae' (testGrad_fst 𝕋 p _))]
    simp_rw [eLpNorm_congr_ae (hae' (testGrad_snd 𝕋 p _ _))]
    exact hC _ ((φ (ns k)).contDiff.of_le (by simp)) (φ (ns k)).hasCompactSupport
  have hlim : Tendsto (fun k => (C : ℝ≥0∞) * ∑ i, eLpNorm ((w (ns k)).snd i : ℝᵈ → ℝ) p) atTop
      (𝓝 (C * ∑ i, eLpNorm ((u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p)) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.coe_ne_top)
    exact tendsto_finsetSum _ fun i _ => (h2 i).comp hns.tendsto_atTop
  have hle : eLpNorm ((u : LpGrad 𝕋 p).fst : ℝᵈ → ℝ) pstar ≤
      C * ∑ i, eLpNorm ((u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p :=
    hfat.trans ((liminf_le_liminf (Eventually.of_forall hk)).trans hlim.liminf_eq.le)
  have hfin : (C : ℝ≥0∞) * ∑ i, eLpNorm ((u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p < ∞ := by
    refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
    refine ENNReal.sum_lt_top.2 fun i _ => ?_
    rw [← injSousCrit_eLpNorm_top]
    exact Lp.eLpNorm_lt_top _
  exact ⟨hle.trans_lt hfin, hle⟩

private lemma injSousCrit_snd_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (v : LpGrad 𝕋 p) (i : Fin d) :
    eLpNorm (v.snd i : ℝᵈ → ℝ) p ≤ ‖v‖₊ := by
  rw [← injSousCrit_eLpNorm_top, ← Lp.enorm_def, enorm_eq_nnnorm, ENNReal.coe_le_coe]
  exact (PiLp.nnnorm_apply_le _ i).trans (WithLp.nnnorm_snd_le _ v)

private lemma injSousCrit_const (C a : ℝ≥0) (x : ℝ≥0∞) :
    (C : ℝ≥0∞) * ∑ _i : Fin d, (a : ℝ≥0∞) * x = ↑(C * d * a) * x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.coe_mul,
    ENNReal.coe_mul, ENNReal.coe_natCast]
  ring

/-- **Cor. `corol:injSousCritOm`, `s = 1`, `p > 1`.** Si `Ω` a la propriété de prolongement de
Sobolev pour `p` (au lieu de « `Ω` régulier », \claudereport), il existe `C = C(p, Ω)` tel que
`‖u‖_{L^{p*}(Ω)} ≤ C ‖u‖_{W^{1,p}(Ω)}` pour tout `u ∈ W^{1,p}(Ω)`.
Preuve : `th_injSousCrit` appliqué au prolongement `P u`, avec `‖P u‖ ≤ ‖P‖ ‖u‖`. -/
theorem corol_injSousCritOm (Ω : TopologicalSpace.Opens ℝᵈ) {p pstar : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hpd : p < d) (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹)
    (hP : ProlongementSobolev Ω p) :
    ∃ C : ℝ≥0, ∀ u : W1p Ω p,
      MemLp ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ∧
        eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ≤
          C * ‖u‖ₑ := by
  obtain ⟨C, hC⟩ := th_injSousCrit hp hpd hpstar
  obtain ⟨P, hPu⟩ := hP
  refine ⟨C * d * ‖P‖₊, fun u => ?_⟩
  have hi : ∀ i, eLpNorm ((P u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p ≤ (‖P‖₊ : ℝ≥0∞) * ‖u‖ₑ := by
    intro i
    refine (injSousCrit_snd_le _ i).trans ?_
    rw [enorm_eq_nnnorm u, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact P.le_opNNNorm u
  have hle : eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ≤
      ↑(C * d * ‖P‖₊) * ‖u‖ₑ := by
    have hPC := (hC (P u)).2
    have e : eLpNorm ((u : LpGrad Ω p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) =
        eLpNorm ((P u : LpGrad 𝕋 p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) :=
      (eLpNorm_congr_ae (hPu u)).symm
    refine e.trans_le ?_
    have h1 : eLpNorm ((P u : LpGrad 𝕋 p).fst : ℝᵈ → ℝ) pstar (volume.restrict (Ω : Set ℝᵈ)) ≤
        eLpNorm ((P u : LpGrad 𝕋 p).fst : ℝᵈ → ℝ) pstar :=
      eLpNorm_mono_measure _ Measure.restrict_le_self
    have h2 : (C : ℝ≥0∞) * ∑ i, eLpNorm ((P u : LpGrad 𝕋 p).snd i : ℝᵈ → ℝ) p ≤
        C * ∑ _i : Fin d, (‖P‖₊ : ℝ≥0∞) * ‖u‖ₑ := by
      gcongr with i; exact hi i
    refine h1.trans (hPC.trans (h2.trans ?_))
    exact (injSousCrit_const C _ _).le
  exact ⟨hle.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top enorm_lt_top), hle⟩

end M1Analyse
