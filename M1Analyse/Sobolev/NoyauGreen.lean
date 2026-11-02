/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Distribution.Distribution

/-!
# §5.3 Injections de Sobolev, cas sous-critique : noyau de Green (`subsec:injSousCrit`)

Source : `Include/Sobolev.tex`, sous-section `subsec:injSousCrit` : `prop:convolPow` et
`corol:noyauGreen` seulement (les autres énoncés de la sous-section sont traités ailleurs).

Conventions. `ℝ^d` est `EuclideanSpace ℝ (Fin d)` muni de la mesure de Lebesgue `volume`, avec
`1 ≤ d` (`d ∈ ℕ*` dans le cours). La mesure d'angle de la sphère `𝕊_{d-1}` est la mesure
Mathlib `(volume : Measure ℝ^d).toSphere`, qui coïncide avec celle du cours,
`μ(A)/d = Leb{ta | a ∈ A, t ∈ ]0,1]}` (`toSphere_eq_cone_Ioc`) ; ainsi
`|𝕊_{d-1}| = volume.toSphere.real univ = d · Leb(B(0,1))` (`Measure.toSphere_real_apply_univ`).
Le gradient est `gradient` de Mathlib, le laplacien `Δ` est `InnerProductSpace.laplacian`
(notation `Δ` de `Laplacian`), la convolution est `MeasureTheory.convolution`
(`f ⋆ g = f ⋆[lsmul ℝ ℝ, volume] g`), les distributions et fonctions test sont
`Distribution` et `TestFunction` de Mathlib (`𝓓'(⊤, ℝ)`, `𝓓(⊤, ℝ)` avec `⊤ = ℝ^d`).

Preuves. `prop:convolPow` suit le cours : coordonnées polaires
(`Measure.measurePreserving_homeomorphUnitSphereProd`), puis théorème fondamental de
l'analyse le long des rayons. Pour `corol:noyauGreen` on évite la formule de Stokes du cours :
on régularise le noyau en `G_ε(x) = c(d) k(|x|² + ε²)` (lisse sur `ℝ^d`), on intègre par parties
sur `ℝ^d` (`∫ G_ε Δφ = -∫ ⟨∇G_ε, ∇φ⟩` avec `∇G_ε(x) = -x / (|𝕊| (|x|² + ε²)^{d/2})`), on passe
à la limite `ε → 0⁺` par convergence dominée des deux côtés, et on conclut par
`prop:convolPow` en `x = 0`.
-/

open Set Filter Topology MeasureTheory Metric Laplacian
open scoped ContDiff Convolution Distributions LineDeriv Pointwise
open ContinuousLinearMap (lsmul)

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- `ℝ^d` est non trivial pour `d ≥ 1`. -/
private theorem nontrivial_euclidean (hd : 1 ≤ d) : Nontrivial ℝᵈ :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)

/-- **Mesure d'angle sur la sphère** (définition du cours, avant `prop:convolPow`). La mesure
Mathlib `volume.toSphere` sur `𝕊_{d-1}` vérifie `μ(A) = d · Leb{ta | a ∈ A, t ∈ ]0,1]}` pour
tout borélien `A ⊂ 𝕊_{d-1}`. -/
theorem toSphere_eq_cone_Ioc (hd : 1 ≤ d) {A : Set (sphere (0 : ℝᵈ) 1)} (hA : MeasurableSet A) :
    (volume : Measure ℝᵈ).toSphere A =
      d * volume {y : ℝᵈ | ∃ a ∈ A, ∃ t ∈ Ioc (0 : ℝ) 1, y = t • (a : ℝᵈ)} := by
  have := nontrivial_euclidean hd
  rw [Measure.toSphere_apply' _ hA, finrank_euclideanSpace_fin]
  congr 1
  refine le_antisymm (measure_mono ?_) ?_
  · rintro _ ⟨t, ht, _, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, t, Ioo_subset_Ioc_self ht, rfl⟩
  · calc volume {y : ℝᵈ | ∃ a ∈ A, ∃ t ∈ Ioc (0 : ℝ) 1, y = t • (a : ℝᵈ)}
        ≤ volume (Ioo (0 : ℝ) 1 • (((↑) : sphere (0 : ℝᵈ) 1 → ℝᵈ) '' A) ∪ sphere 0 1) := by
          refine measure_mono ?_
          rintro _ ⟨a, ha, t, ht, rfl⟩
          rcases ht.2.lt_or_eq with h | rfl
          · exact Or.inl ⟨t, ⟨ht.1, h⟩, _, ⟨a, ha, rfl⟩, rfl⟩
          · exact Or.inr (by simp)
      _ ≤ _ := by
          refine (measure_union_le _ _).trans ?_
          rw [Measure.addHaar_sphere, add_zero]

/-- **Point technique (Coordonnées polaires).** Pour `g ∈ L^1(ℝ^d)`,
`∫_{ℝ^d} g = ∫_{𝕊} ∫_0^∞ r^{d-1} g(r z) dr dz`, où `dz` est la mesure de surface sur la
sphère unité (définie dans Mathlib comme image de la mesure de Lebesgue). Utilisé pour
`corol:noyauGreen`, `prop:convolPow`. -/
theorem integral_polaire (hd : 1 ≤ d) {g : ℝᵈ → ℝ} (hg : Integrable g) :
    ∫ y, g y = ∫ z, (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * g (r • (z : ℝᵈ)))
      ∂(volume : Measure ℝᵈ).toSphere := by
  have := nontrivial_euclidean hd
  have hmp := (volume : Measure ℝᵈ).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_euclideanSpace_fin] at hmp
  set F : (sphere (0 : ℝᵈ) 1 × Ioi (0 : ℝ)) → ℝ :=
    fun p => g ((homeomorphUnitSphereProd ℝᵈ).symm p : ℝᵈ) with hF
  have hFe : ∀ x : ({0}ᶜ : Set ℝᵈ), F (homeomorphUnitSphereProd ℝᵈ x) = g x := fun x => by
    simp only [hF, Homeomorph.symm_apply_apply]
  have hint :
      Integrable F ((volume : Measure ℝᵈ).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
    rw [← hmp.integrable_comp_emb (homeomorphUnitSphereProd ℝᵈ).measurableEmbedding]
    have : F ∘ homeomorphUnitSphereProd ℝᵈ = g ∘ (↑) := funext hFe
    rw [this, ← integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl]
    exact hg.integrableOn
  calc ∫ y, g y = ∫ y : ({0}ᶜ : Set ℝᵈ), g y ∂((volume : Measure ℝᵈ).comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ g x,
          restrict_compl_singleton]
    _ = ∫ p, F p ∂((volume : Measure ℝᵈ).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
        rw [← hmp.integral_comp (homeomorphUnitSphereProd ℝᵈ).measurableEmbedding]
        simp only [hFe]
    _ = ∫ z, ∫ r, F (z, r) ∂(Measure.volumeIoiPow (d - 1)) ∂(volume : Measure ℝᵈ).toSphere :=
        integral_prod F hint
    _ = _ := by
        congr 1
        ext z
        simp only [Measure.volumeIoiPow, ENNReal.ofReal, hF,
          homeomorphUnitSphereProd_symm_apply_coe]
        rw [integral_withDensity_eq_integral_smul, integral_subtype_comap measurableSet_Ioi
          (fun a ↦ Real.toNNReal (a ^ (d - 1)) • g (a • (z : ℝᵈ)))]
        · refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
          rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
        · exact (measurable_subtype_coe.pow_const _).real_toNNReal


/-- `x ↦ |x|^{1-d}` est intégrable sur toute boule `B(0,R)` de `ℝ^d`. -/
private theorem integrableOn_ball_norm_rpow (hd : 1 ≤ d) (R : ℝ) :
    IntegrableOn (fun y : ℝᵈ => ‖y‖ ^ ((1 : ℝ) - d)) (ball 0 R) := by
  have := nontrivial_euclidean hd
  rw [integrableOn_fun_norm_addHaar volume (f := fun r : ℝ => r ^ ((1 : ℝ) - d)),
    finrank_euclideanSpace_fin]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hy0, Nat.cast_sub hd]
  simp

/-- `|𝕊_{d-1}| > 0`. -/
private theorem toSphere_real_univ_pos (hd : 1 ≤ d) :
    0 < (volume : Measure ℝᵈ).toSphere.real univ := by
  have := nontrivial_euclidean hd
  rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  refine mul_pos (by exact_mod_cast hd) ?_
  exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

/-- Cœur de la preuve de `prop:convolPow` (cas `x = 0`) :
`∫ ⟨∇F(y), y⟩ / |y|^d dy = -|𝕊_{d-1}| F(0)` pour `F ∈ C¹_c(ℝ^d)`. -/
private theorem integral_fderiv_div_pow (hd : 1 ≤ d) {F : ℝᵈ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFc : HasCompactSupport F) :
    ∫ y, fderiv ℝ F y y / ‖y‖ ^ d = - ((volume : Measure ℝᵈ).toSphere.real univ * F 0) := by
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_closedBall (0 : ℝᵈ)
  obtain ⟨C, hC⟩ := (hF.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hFc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hF0 : ∀ y, R < ‖y‖ → fderiv ℝ F y = 0 := fun y hy => by
    by_contra h
    have := hR (support_fderiv_subset ℝ h)
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  have hint : Integrable (fun y : ℝᵈ => fderiv ℝ F y y / ‖y‖ ^ d) := by
    refine Integrable.mono' (((integrableOn_ball_norm_rpow hd (R + 1)).integrable_indicator
      measurableSet_ball).const_mul C) ?_ (ae_of_all _ fun y => ?_)
    · exact (((hF.continuous_fderiv one_ne_zero).clm_apply continuous_id).measurable.div
        (continuous_norm.pow d).measurable).aestronglyMeasurable
    · by_cases hy : y ∈ ball (0 : ℝᵈ) (R + 1)
      · rw [indicator_of_mem hy]
        rcases eq_or_ne y 0 with rfl | hy0
        · simp only [map_zero, zero_div, norm_zero]
          exact mul_nonneg hC0 (Real.rpow_nonneg le_rfl _)
        have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
        rw [norm_div, norm_pow, norm_norm, div_le_iff₀ (by positivity), mul_assoc,
          ← Real.rpow_natCast, ← Real.rpow_add hn]
        simp only [sub_add_cancel, Real.rpow_one]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC y) (norm_nonneg _))
      · rw [indicator_of_notMem hy]
        rw [mem_ball, dist_zero_right, not_lt] at hy
        simp [hF0 y (by linarith)]
  rw [integral_polaire hd hint]
  have hinner : ∀ z : sphere (0 : ℝᵈ) 1,
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (fderiv ℝ F (r • (z : ℝᵈ)) (r • (z : ℝᵈ)) /
        ‖r • (z : ℝᵈ)‖ ^ d) = - F 0 := by
    intro z
    have hz : ‖(z : ℝᵈ)‖ = 1 := by simp
    have hcongr : ∀ r ∈ Ioi (0 : ℝ), r ^ (d - 1) * (fderiv ℝ F (r • (z : ℝᵈ)) (r • (z : ℝᵈ)) /
        ‖r • (z : ℝᵈ)‖ ^ d) = fderiv ℝ F (r • (z : ℝᵈ)) z := by
      intro r (hr : 0 < r)
      rw [map_smul, norm_smul, hz, Real.norm_of_nonneg hr.le, mul_one, smul_eq_mul]
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      simp only [add_tsub_cancel_right, pow_succ]
      field_simp
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have hd' : ∀ r : ℝ, HasDerivAt (fun r : ℝ => F (r • (z : ℝᵈ)))
        (fderiv ℝ F (r • (z : ℝᵈ)) z) r := fun r => by
      have := ((hF.differentiable one_ne_zero) (r • (z : ℝᵈ))).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).smul_const (z : ℝᵈ))
      simp only [one_smul] at this
      exact this
    have hcont : Continuous (fun r : ℝ => fderiv ℝ F (r • (z : ℝᵈ)) z) :=
      ((hF.continuous_fderiv one_ne_zero).comp (continuous_id.smul continuous_const)).clm_apply
        continuous_const
    have hsupp : HasCompactSupport (fun r : ℝ => fderiv ℝ F (r • (z : ℝᵈ)) z) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun r hr => ?_
      rw [mem_closedBall, dist_zero_right, not_le] at hr
      rw [hF0 _ (by rwa [norm_smul, hz, mul_one])]
      rfl
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun r : ℝ => F (r • (z : ℝᵈ))) (m := 0)
      (hd' 0).continuousAt.continuousWithinAt (fun r _ => hd' r)
      (hcont.integrable_of_hasCompactSupport hsupp).integrableOn]
    · simp
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop R] with r hr
      refine (image_eq_zero_of_notMem_tsupport fun h => ?_).symm
      have := hR h
      rw [mem_closedBall, dist_zero_right, norm_smul, hz, mul_one, Real.norm_eq_abs] at this
      linarith [le_abs_self r]
  simp only [hinner, integral_const, smul_eq_mul, mul_neg]


/-- **Prop. `prop:convolPow`.** Pour tous `f ∈ C¹_c(ℝ^d)` et `x ∈ ℝ^d`,
`f(x) = (1/|𝕊_{d-1}|) ∫_{ℝ^d} ⟨∇f(x-y), y/‖y‖^d⟩ dy`.
Remarque : on suppose `d ≥ 1` (`d ∈ ℕ*` dans le cours ; l'énoncé est faux pour `d = 0`).
L'intégrande, non défini en `y = 0`, y vaut `0` par convention de Lean (ensemble négligeable). -/
theorem prop_convolPow (hd : 1 ≤ d) {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (x : ℝᵈ) :
    f x = 1 / (volume : Measure ℝᵈ).toSphere.real univ *
      ∫ y, inner ℝ (gradient f (x - y)) ((‖y‖ ^ d)⁻¹ • y) := by
  have hσ := toSphere_real_univ_pos hd
  have key := integral_fderiv_div_pow hd (F := fun y => f (x + y))
    (hf.comp (contDiff_const.add contDiff_id)) (hfc.comp_homeomorph (Homeomorph.addLeft x))
  have h1 : ∫ y, inner ℝ (gradient f (x - y)) ((‖y‖ ^ d)⁻¹ • y) =
      - ∫ y, fderiv ℝ (fun y => f (x + y)) y y / ‖y‖ ^ d := by
    rw [← integral_neg_eq_self, ← integral_neg]
    congr 1
    ext y
    simp only [sub_neg_eq_add, norm_neg, smul_neg, inner_neg_right, inner_smul_right, gradient,
      InnerProductSpace.toDual_symm_apply, fderiv_comp_add_left]
    ring
  rw [h1, key]
  simp only [add_zero]
  field_simp


/-- Profil radial (auxiliaire) du noyau de Green, en fonction de `t = |x|²` :
`-t^{1/2}` si `d = 1`, `-(1/2) ln t` si `d = 2`, `t^{(2-d)/2}` si `d ≥ 3`. -/
private noncomputable def profilGreen (d : ℕ) (t : ℝ) : ℝ :=
  if d = 1 then -t ^ (1 / 2 : ℝ) else if d = 2 then -(1 / 2) * Real.log t
  else t ^ ((2 - d) / 2 : ℝ)

/-- `k'(t) = -(max{1,d-2}/2) t^{-d/2}`. -/
private theorem hasDerivAt_profilGreen (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (profilGreen d) (-(max 1 ((d : ℝ) - 2) / 2) * t ^ (-(d : ℝ) / 2)) t := by
  unfold profilGreen
  split_ifs with h1 h2
  · subst h1
    convert (Real.hasDerivAt_rpow_const (p := 1 / 2) (Or.inl ht.ne')).neg using 1
    norm_num
  · subst h2
    convert ((Real.hasDerivAt_log ht.ne').const_mul (-(1 / 2 : ℝ))) using 1
    rw [show (-(2 : ℕ) : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  · have h3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    convert Real.hasDerivAt_rpow_const (p := (2 - d) / 2) (Or.inl ht.ne') using 1
    rw [max_eq_right (by linarith)]
    congr 1
    · ring
    · congr 1; ring

/-- Majoration uniforme du profil, pour la convergence dominée. -/
private theorem abs_profilGreen_le (hd : 1 ≤ d) {r R ε : ℝ} (hr : 0 < r) (hrR : r < R) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    |profilGreen d (r ^ 2 + ε ^ 2)| ≤
      ((R ^ 2 + 1) ^ (1 / 2 : ℝ) + Real.log (R ^ 2 + 1)) + (2 + R) * r ^ ((1 : ℝ) - d) := by
  have hR : 0 < R := hr.trans hrR
  have hs : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hsR : r ^ 2 + ε ^ 2 ≤ R ^ 2 + 1 := by nlinarith
  have hlog : 0 ≤ Real.log (R ^ 2 + 1) := Real.log_nonneg (by nlinarith)
  have hsq : 0 ≤ (R ^ 2 + 1) ^ (1 / 2 : ℝ) := by positivity
  have hrp : 0 ≤ r ^ ((1 : ℝ) - d) := by positivity
  have hB : 0 ≤ (2 + R) * r ^ ((1 : ℝ) - d) := by positivity
  unfold profilGreen
  split_ifs with h1 h2
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    have := Real.rpow_le_rpow hs.le hsR (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  · subst h2
    have hr1 : r ^ ((1 : ℝ) - (2 : ℕ)) = r⁻¹ := by
      rw [show (1 : ℝ) - (2 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
    rw [hr1]
    have hup : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log (R ^ 2 + 1) := Real.log_le_log hs hsR
    have hlow : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hlr : -Real.log r ≤ r⁻¹ := by
      rw [← Real.log_inv]
      linarith [Real.log_le_sub_one_of_pos (inv_pos.2 hr)]
    rw [Real.log_pow] at hlow
    have hri : 0 ≤ r⁻¹ := by positivity
    have hRr := mul_nonneg hR.le hri
    push_cast at hlow
    rw [abs_le]
    constructor <;> nlinarith
  · have h3 : (3 : ℝ) ≤ d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (by positivity)]
    have h1 := Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith : r ^ 2 ≤ r ^ 2 + ε ^ 2)
      (by linarith : ((2 : ℝ) - d) / 2 ≤ 0)
    have h2 : (r ^ 2) ^ (((2 : ℝ) - d) / 2) = r * r ^ ((1 : ℝ) - d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_one_add' hr.le (by
        linarith)]
      congr 1; push_cast; ring
    rw [h2] at h1
    have : r * r ^ ((1 : ℝ) - d) ≤ (2 + R) * r ^ ((1 : ℝ) - d) :=
      mul_le_mul_of_nonneg_right (by linarith) hrp
    linarith


/-- La constante `c(d) := 1/(max{1, d-2} |𝕊_{d-1}|)` de `corol:noyauGreen`. -/
noncomputable def constGreen (d : ℕ) : ℝ :=
  1 / (max 1 ((d : ℝ) - 2) * (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere.real univ)

/-- Le noyau de Green `G : ℝ^d → ℝ` de `corol:noyauGreen` :
`G(x) := c(d) · (-|x|` si `d = 1`, `-ln |x|` si `d = 2`, `|x|^{2-d}` si `d ≥ 3)`.
Remarque : la valeur en `x = 0` (non définie dans le cours) est celle donnée par les
conventions de Lean (`ln 0 = 0`, `0^{2-d} = 0`) ; elle est sans importance (point négligeable). -/
noncomputable def noyauGreen (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  constGreen d * (if d = 1 then -‖x‖ else if d = 2 then -Real.log ‖x‖ else ‖x‖ ^ ((2 : ℝ) - d))

/-- `G(x) = c(d) k(|x|²)` pour `x ≠ 0`. -/
private theorem noyauGreen_eq_profil {x : ℝᵈ} (hx : x ≠ 0) :
    noyauGreen d x = constGreen d * profilGreen d (‖x‖ ^ 2) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have key : ∀ a : ℝ, (‖x‖ ^ 2) ^ a = ‖x‖ ^ (2 * a) := fun a => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  unfold noyauGreen profilGreen
  congr 1
  split_ifs
  · rw [key]; norm_num
  · rw [Real.log_pow]; push_cast; ring
  · rw [key]; congr 1; ring

/-- Noyau de Green régularisé (auxiliaire) : `G_ε(x) = c(d) k(|x|² + ε²)`. -/
private noncomputable def greenReg (d : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  constGreen d * profilGreen d (‖x‖ ^ 2 + ε ^ 2)

/-- Différentielle de `G_ε`. -/
private theorem hasFDerivAt_greenReg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (x : ℝᵈ) :
    HasFDerivAt (greenReg d ε) ((constGreen d * (-(max 1 ((d : ℝ) - 2) / 2) *
      (‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2))) • (2 • (innerSL ℝ x).comp
        (ContinuousLinearMap.id ℝ ℝᵈ))) x := by
  have hs : HasFDerivAt (fun y : ℝᵈ => ‖y‖ ^ 2 + ε ^ 2)
      (2 • (innerSL ℝ x).comp (ContinuousLinearMap.id ℝ ℝᵈ)) x :=
    ((hasFDerivAt_id x).norm_sq).add_const _
  have := ((hasDerivAt_profilGreen hd (by positivity : 0 < ‖x‖ ^ 2 + ε ^ 2)).comp_hasFDerivAt
    x hs).const_mul (constGreen d)
  rw [smul_smul] at this
  exact this

/-- `∇G_ε(x) = -x / (|𝕊_{d-1}| (|x|² + ε²)^{d/2})`. -/
private theorem fderiv_greenReg_apply (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) (x v : ℝᵈ) :
    fderiv ℝ (greenReg d ε) x v = -(1 / (volume : Measure ℝᵈ).toSphere.real univ) *
      (‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2) * inner ℝ x v := by
  rw [(hasFDerivAt_greenReg hd hε x).fderiv]
  have hσ := toSphere_real_univ_pos hd
  have hm : 0 < max 1 ((d : ℝ) - 2) := lt_max_of_lt_left one_pos
  simp only [constGreen]
  simp
  field_simp

/-- Base orthonormée canonique de `ℝ^d`. -/
local notation "𝐞" => EuclideanSpace.basisFun (Fin d) ℝ

/-- `Δu = ∑_i ∂_i ∂_i u` pour `u ∈ C²(ℝ^d)`. -/
private theorem laplacian_eq_sum {u : ℝᵈ → ℝ} (hu : ContDiff ℝ 2 u) (x : ℝᵈ) :
    Δ u x = ∑ i, fderiv ℝ (fun y => fderiv ℝ u y (𝐞 i)) x (𝐞 i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u 𝐞]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiff : DifferentiableAt ℝ (fderiv ℝ u) x :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hdiff (differentiableAt_const _)]
  simp


/-- `G_ε` est continu. -/
private theorem continuous_greenReg (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) : Continuous (greenReg d ε) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_greenReg hd hε x).continuousAt

/-- `x ↦ (|x|² + ε²)^a` est continu. -/
private theorem continuous_regPow {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous fun x : ℝᵈ => (‖x‖ ^ 2 + ε ^ 2) ^ a :=
  (by fun_prop : Continuous fun x : ℝᵈ => ‖x‖ ^ 2 + ε ^ 2).rpow_const
    fun x => Or.inl (by positivity)

/-- Intégration par parties pour le noyau régularisé :
`∫ G_ε Δφ = (1/|𝕊_{d-1}|) ∫ (|x|² + ε²)^{-d/2} ⟨∇φ(x), x⟩ dx`. -/
private theorem integral_greenReg_mul_lapl (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) {φ : ℝᵈ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, greenReg d ε x * ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (𝐞 i)) x (𝐞 i) =
      (1 / (volume : Measure ℝᵈ).toSphere.real univ) *
        ∫ x, (‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2) * fderiv ℝ φ x x := by
  set σ := (volume : Measure ℝᵈ).toSphere.real univ
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ v : ℝᵈ, ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) := fun v =>
    hφ1.clm_apply contDiff_const
  have hψc : ∀ v : ℝᵈ, HasCompactSupport (fun y => fderiv ℝ φ y v) := fun v =>
    hφc.fderiv_apply (𝕜 := ℝ) v
  have hψ' : ∀ v w : ℝᵈ, Continuous (fun y => fderiv ℝ (fun y => fderiv ℝ φ y v) y w) :=
    fun v w => ((hψ v).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hψ'c : ∀ v w : ℝᵈ, HasCompactSupport (fun y => fderiv ℝ (fun y => fderiv ℝ φ y v) y w) :=
    fun v w => (hψc v).fderiv_apply (𝕜 := ℝ) w
  have hG := continuous_greenReg hd hε
  have hG' : ∀ v : ℝᵈ, Continuous (fun x => fderiv ℝ (greenReg d ε) x v) := fun v => by
    simp_rw [fderiv_greenReg_apply hd hε]
    exact (continuous_const.mul (continuous_regPow hε _)).mul
      (continuous_id.inner continuous_const)
  have hint : ∀ {f g : ℝᵈ → ℝ}, Continuous f → Continuous g → HasCompactSupport g →
      Integrable (fun x => f x * g x) := fun hf hg hgc =>
    (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint hG (hψ' _ _) (hψ'c _ _)]
  have hibp : ∀ i, ∫ x, greenReg d ε x * fderiv ℝ (fun y => fderiv ℝ φ y (𝐞 i)) x (𝐞 i) =
      ∫ x, (1 / σ) * ((‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2) * (inner ℝ (𝐞 i) x •
        fderiv ℝ φ x (𝐞 i))) := fun i => by
    rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hint (hG' _) (hψ _).continuous
      (hψc _)) (hint hG (hψ' _ _) (hψ'c _ _)) (hint hG (hψ _).continuous (hψc _))
      (fun x _ => (hasFDerivAt_greenReg hd hε x).differentiableAt)
      (fun x _ => ((hψ _).differentiable one_ne_zero) x), ← integral_neg]
    congr 1
    ext x
    rw [fderiv_greenReg_apply hd hε, real_inner_comm, smul_eq_mul]
    ring
  simp_rw [hibp]
  rw [← integral_finsetSum _ fun i _ => ?_, ← integral_const_mul]
  · congr 1
    ext x
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simp_rw [← map_smul, ← map_sum, OrthonormalBasis.sum_repr']
  · refine Integrable.const_mul ?_ _
    simp_rw [smul_eq_mul, ← mul_assoc]
    exact hint ((continuous_regPow hε _).mul (continuous_const.inner continuous_id))
      (hψ _).continuous (hψc _)


/-- **Point technique (`-ΔG = δ₀`, forme intégrée).** Pour `φ ∈ C²_c(ℝ^d)`,
`∫ G Δφ = -φ(0)` (laplacien écrit comme `∑_i ∂_i ∂_i φ`). Démontré en coordonnées polaires,
par intégration en `r` sur chaque rayon. Utilisé pour `corol:noyauGreen`. -/
theorem integral_noyauGreen_mul_lapl (hd : 1 ≤ d) {φ : ℝᵈ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ x, noyauGreen d x * ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (𝐞 i)) x (𝐞 i) = -φ 0 := by
  have := nontrivial_euclidean hd
  set σ := (volume : Measure ℝᵈ).toSphere.real univ
  have hσ : 0 < σ := toSphere_real_univ_pos hd
  set L : ℝᵈ → ℝ := fun x => ∑ i, fderiv ℝ (fun y => fderiv ℝ φ y (𝐞 i)) x (𝐞 i) with hL
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ v : ℝᵈ, ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) := fun v =>
    hφ1.clm_apply contDiff_const
  have hLc : Continuous L := continuous_finsetSum _ fun i _ =>
    ((hψ _).continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- support
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall (0 : ℝᵈ)
  set R' := max R 0 + 1
  have hR'0 : 0 < R' := by positivity
  have hRR' : R < R' := by have := le_max_left R 0; linarith
  have hout : ∀ x : ℝᵈ, x ∉ ball (0 : ℝᵈ) R' → x ∉ tsupport φ := fun x hx h => by
    have := hR h
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_ball, dist_zero_right, not_lt] at hx
    linarith
  have hL0 : ∀ x, x ∉ ball (0 : ℝᵈ) R' → L x = 0 := fun x hx => by
    refine Finset.sum_eq_zero fun i _ => ?_
    by_contra h
    refine hout x hx ?_
    exact tsupport_fderiv_apply_subset ℝ (𝐞 i)
      (tsupport_fderiv_apply_subset ℝ (𝐞 i) (subset_tsupport _ h))
  have hD0 : ∀ x, x ∉ ball (0 : ℝᵈ) R' → fderiv ℝ φ x = 0 := fun x hx => by
    by_contra h
    exact hout x hx (support_fderiv_subset ℝ h)
  obtain ⟨M, hM⟩ := hLc.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℝᵈ) R') fun x hx =>
      hL0 x fun h => hx (ball_subset_closedBall h))
  obtain ⟨C, hC⟩ := (hφ1.continuous).bounded_above_of_compact_support (hφc.fderiv (𝕜 := ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hne : ∀ᵐ x ∂(volume : Measure ℝᵈ), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  set A := (R' ^ 2 + 1) ^ (1 / 2 : ℝ) + Real.log (R' ^ 2 + 1)
  set B := 2 + R'
  have hA : 0 ≤ A := add_nonneg (by positivity) (Real.log_nonneg (by nlinarith))
  have hB : 0 ≤ B := by positivity
  have hpow := integrableOn_ball_norm_rpow hd R'
  -- limite du membre de gauche
  have h1 : Tendsto (fun ε => ∫ x, greenReg d ε x * L x) (𝓝[>] 0)
      (𝓝 (∫ x, noyauGreen d x * L x)) := by
    refine tendsto_integral_filter_of_dominated_convergence ((ball (0 : ℝᵈ) R').indicator
      fun x => |constGreen d| * (A + B * ‖x‖ ^ ((1 : ℝ) - d)) * M) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((continuous_greenReg hd hε).mul hLc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε hε1
      filter_upwards [hne] with x hx
      by_cases hxb : x ∈ ball (0 : ℝᵈ) R'
      · rw [indicator_of_mem hxb, norm_mul, greenReg, norm_mul, Real.norm_eq_abs,
          Real.norm_eq_abs]
        refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (hM x) (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (add_nonneg hA (mul_nonneg hB (by positivity))))
        rw [mem_ball, dist_zero_right] at hxb
        exact abs_profilGreen_le hd (norm_pos_iff.2 hx) hxb (le_of_lt hε) hε1.2.le
      · rw [indicator_of_notMem hxb, hL0 x hxb, mul_zero, norm_zero]
    · exact IntegrableOn.integrable_indicator
        ((((integrableOn_const measure_ball_lt_top.ne).add (hpow.const_mul B)).const_mul
          _).mul_const _) measurableSet_ball
    · filter_upwards [hne] with x hx
      rw [noyauGreen_eq_profil hx]
      refine Tendsto.mul_const _ (Tendsto.const_mul _ ?_)
      have hpos : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.2 hx; positivity
      refine ((hasDerivAt_profilGreen hd hpos).continuousAt.tendsto.comp ?_)
      refine tendsto_nhdsWithin_of_tendsto_nhds ?_
      have hc : Continuous fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2 := by fun_prop
      simpa using hc.tendsto 0
  -- limite du membre de droite
  have h2 : Tendsto (fun ε => (1 / σ) * ∫ x, (‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2) *
      fderiv ℝ φ x x) (𝓝[>] 0) (𝓝 ((1 / σ) * ∫ x, fderiv ℝ φ x x / ‖x‖ ^ d)) := by
    refine Tendsto.const_mul _ ?_
    refine tendsto_integral_filter_of_dominated_convergence ((ball (0 : ℝᵈ) R').indicator
      fun x => C * ‖x‖ ^ ((1 : ℝ) - d)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact ((continuous_regPow hε _).mul
        (hφ1.continuous.clm_apply continuous_id)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      filter_upwards [hne] with x hx
      by_cases hxb : x ∈ ball (0 : ℝᵈ) R'
      · rw [indicator_of_mem hxb, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
        have hle := Real.rpow_le_rpow_of_nonpos (by positivity)
          (by nlinarith : ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 + ε ^ 2) (by
            have : (0 : ℝ) ≤ d := by positivity
            linarith : -(d : ℝ) / 2 ≤ 0)
        have heq : (‖x‖ ^ 2) ^ (-(d : ℝ) / 2) * ‖x‖ = ‖x‖ ^ ((1 : ℝ) - d) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
          nth_rewrite 2 [← Real.rpow_one ‖x‖]
          rw [← Real.rpow_add hn]
          congr 1; push_cast; ring
        calc (‖x‖ ^ 2 + ε ^ 2) ^ (-(d : ℝ) / 2) * ‖fderiv ℝ φ x x‖
            ≤ (‖x‖ ^ 2) ^ (-(d : ℝ) / 2) * (C * ‖x‖) :=
              mul_le_mul hle ((ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _))) (norm_nonneg _)
                (by positivity)
          _ = C * ‖x‖ ^ ((1 : ℝ) - d) := by rw [← heq]; ring
      · rw [indicator_of_notMem hxb, hD0 x hxb]
        simp
    · exact IntegrableOn.integrable_indicator (hpow.const_mul C) measurableSet_ball
    · filter_upwards [hne] with x hx
      have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
      have heq : fderiv ℝ φ x x / ‖x‖ ^ d =
          (‖x‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-(d : ℝ) / 2) * fderiv ℝ φ x x := by
        have h' : (‖x‖ ^ 2 : ℝ) ^ (-(d : ℝ) / 2) = (‖x‖ ^ d)⁻¹ := by
          rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul hn.le, ← Real.rpow_natCast ‖x‖ d,
            ← Real.rpow_neg hn.le]
          congr 1; push_cast; ring
        rw [zero_pow two_ne_zero, add_zero, h', div_eq_mul_inv, mul_comm]
      rw [heq]
      refine Tendsto.mul_const _ (tendsto_nhdsWithin_of_tendsto_nhds ?_)
      exact ((continuous_const.add (continuous_pow 2)).rpow_const
        fun ε => Or.inl (by positivity : ‖x‖ ^ 2 + ε ^ 2 ≠ 0)).tendsto 0
  have h3 := h2.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (integral_greenReg_mul_lapl hd hε hφ hφc).symm)
  have h4 : ∫ x, fderiv ℝ φ x x / ‖x‖ ^ d = -(σ * φ 0) :=
    integral_fderiv_div_pow hd (hφ.of_le (by norm_num)) hφc
  rw [tendsto_nhds_unique h1 h3, h4]
  field_simp


/-- **Cor. `corol:noyauGreen` (Noyau de Green), `-ΔG = δ₀` sous forme intégrale.**
Pour toute `φ ∈ 𝓓(ℝ^d)` (`C^∞` à support compact), `⟨G, -Δφ⟩ = ∫ G(x) (-Δφ)(x) dx = φ(0)`,
i.e. `-ΔG = δ₀` au sens des distributions. Remarque : on suppose `d ≥ 1`.
Preuve (différente du cours) : sans formule de Stokes ; régularisation
`G_ε(x) = c(d) k(|x|² + ε²)`, intégration par parties sur `ℝ^d`, convergence dominée
(`ε → 0⁺`), puis `prop:convolPow` en `x = 0`. -/
theorem corol_noyauGreen (hd : 1 ≤ d) {φ : ℝᵈ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, noyauGreen d x * (-Δ φ x) = φ 0 := by
  simp_rw [laplacian_eq_sum (hφ.of_le (by norm_cast)), mul_neg, integral_neg,
    integral_noyauGreen_mul_lapl hd (hφ.of_le (by norm_cast)) hφc, neg_neg]

/-- `G` est mesurable. -/
theorem measurable_noyauGreen : Measurable (noyauGreen d) := by
  unfold noyauGreen
  by_cases h1 : d = 1
  · simp only [h1, ↓reduceIte]; fun_prop
  · by_cases h2 : d = 2
    · simp only [h2, OfNat.ofNat_ne_one, ↓reduceIte]; fun_prop
    · simp only [h1, h2, ↓reduceIte]; fun_prop

/-- **Point technique (`G ∈ L^1_loc(ℝ^d)`).** Le noyau de Green est localement intégrable, de
sorte que la distribution associée à `G` et la convolution `G ⋆ φ` sont bien définies.
Utilisé pour `corol:noyauGreen`. -/
theorem locallyIntegrable_noyauGreen (hd : 1 ≤ d) : LocallyIntegrable (noyauGreen d) := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR0, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℝᵈ)
  refine IntegrableOn.mono_set ?_ hR
  set A := (R ^ 2 + 1) ^ (1 / 2 : ℝ) + Real.log (R ^ 2 + 1)
  have hne : ∀ᵐ x ∂(volume : Measure ℝᵈ), x ≠ 0 := by
    have := nontrivial_euclidean hd
    simp [ae_iff, measure_singleton]
  refine Integrable.mono' (g := fun x => |constGreen d| * (A + (2 + R) * ‖x‖ ^ ((1 : ℝ) - d)))
    (((integrableOn_const (C := A) measure_ball_lt_top.ne).add
    ((integrableOn_ball_norm_rpow hd R).const_mul (2 + R))).const_mul |constGreen d|)
    measurable_noyauGreen.aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hne] with x hx hxb
  rw [noyauGreen_eq_profil hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [mem_ball, dist_zero_right] at hxb
  have := abs_profilGreen_le hd (norm_pos_iff.2 hx) hxb le_rfl zero_le_one
  rw [zero_pow two_ne_zero, add_zero] at this
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- Dérivée directionnelle d'une fonction test. -/
private theorem testFunction_lineDerivOp_apply (ψ : 𝓓(⊤, ℝ)) (v x : ℝᵈ) :
    (∂_{v} ψ : 𝓓(⊤, ℝ)) x = fderiv ℝ ψ x v := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_apply_of_le le_top,
    ((ψ.contDiff.differentiable (by simp)) x).lineDeriv_eq_fderiv]

/-- **Cor. `corol:noyauGreen` (Noyau de Green), `-ΔG = δ₀` dans `𝓓'(ℝ^d)`.** Avec les
distributions de Mathlib : `-Δ U_G = δ₀`, où `U_G = Distribution.ofFun ⊤ G volume ⊤` est la
distribution associée à `G ∈ L¹_loc` et `Δ = LineDeriv.laplacianCLM` est le laplacien
distributionnel `∑_i ∂_i ∂_i`. Remarque : on suppose `d ≥ 1`.
Preuve (différente du cours) : déduit de la forme intégrale (`corol_noyauGreen`, preuve par
régularisation de `G`), sans établir `∇G = -V` au sens des distributions. -/
theorem corol_noyauGreen_distrib (hd : 1 ≤ d) :
    -(LineDeriv.laplacianCLM ℝ ℝᵈ 𝓓'(⊤, ℝ) (Distribution.ofFun ⊤ (noyauGreen d) volume ⊤)) =
      Distribution.delta 0 := by
  ext φ
  rw [LineDeriv.laplacianCLM_eq_sum 𝐞]
  simp only [neg_apply, sum_apply]
  rw [Finset.sum_congr rfl fun i _ => Distribution.lineDerivOp_apply_apply _ _ _]
  simp only [Distribution.lineDerivOp_apply_apply, LineDeriv.lineDerivOp_neg, neg_neg]
  rw [← map_sum, Distribution.ofFun_apply
    ((locallyIntegrable_noyauGreen hd).locallyIntegrableOn _)]
  have h2 : ∀ (v : ℝᵈ) (x : ℝᵈ), (∂_{v} (∂_{v} φ) : 𝓓(⊤, ℝ)) x =
      fderiv ℝ (fun y => fderiv ℝ φ y v) x v := fun v x => by
    rw [testFunction_lineDerivOp_apply]
    congr 2
  simp only [sum_apply, smul_eq_mul, Distribution.delta_apply, h2]
  simp_rw [mul_comm _ (noyauGreen d _)]
  rw [integral_noyauGreen_mul_lapl hd (φ.contDiff.of_le (by simp)) φ.hasCompactSupport, neg_neg]

/-- `∂_v (G ⋆ ψ) = G ⋆ ∂_v ψ` pour `ψ ∈ C¹_c`. -/
private theorem fderiv_convolution_apply (hd : 1 ≤ d) {ψ : ℝᵈ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (x v : ℝᵈ) :
    fderiv ℝ (noyauGreen d ⋆ ψ) x v = (noyauGreen d ⋆ fun z => fderiv ℝ ψ z v) x := by
  rw [(hψc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) (locallyIntegrable_noyauGreen hd) hψ
    x).fderiv, convolution_precompR_apply (hf := locallyIntegrable_noyauGreen hd)
    (hcg := hψc.fderiv (𝕜 := ℝ)) (hg := hψ.continuous_fderiv one_ne_zero)]

/-- **Cor. `corol:noyauGreen` (Noyau de Green), seconde partie.** Pour toute `φ ∈ 𝓓(ℝ^d)`,
`G ⋆ φ` est `C^∞` et `φ = -Δ(G ⋆ φ)`.
Remarque : `G ⋆ φ` est la convolution usuelle `(G ⋆ φ)(x) = ∫ G(y) φ(x-y) dy` de la fonction
`G ∈ L¹_loc` avec `φ`, qui coïncide avec la convolution distribution–fonction test du cours
(`def:convolDistrib`) ; l'égalité est ponctuelle. On suppose `d ≥ 1`.
Preuve (différente du cours) : dérivation sous l'intégrale (`∂_v (G ⋆ ψ) = G ⋆ ∂_v ψ`) et forme
intégrale appliquée à `φ(x + ·)`, au lieu de `(-ΔG) ⋆ φ = δ₀ ⋆ φ` (`prop:convolDistrib`). -/
theorem corol_noyauGreen_convol (hd : 1 ≤ d) {φ : ℝᵈ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (noyauGreen d ⋆ φ) ∧ ∀ x, φ x = -Δ (noyauGreen d ⋆ φ) x := by
  have hG := locallyIntegrable_noyauGreen hd
  have hconv := hφc.contDiff_convolution_right (lsmul ℝ ℝ) hG hφ
  refine ⟨hconv, fun x => ?_⟩
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (by norm_cast)
  have hφ1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ2.fderiv_right (m := 1) (by norm_num)
  have hψ : ∀ v : ℝᵈ, ContDiff ℝ 1 (fun y => fderiv ℝ φ y v) := fun v =>
    hφ1.clm_apply contDiff_const
  have hψc : ∀ v : ℝᵈ, HasCompactSupport (fun y => fderiv ℝ φ y v) := fun v =>
    hφc.fderiv_apply (𝕜 := ℝ) v
  rw [laplacian_eq_sum (hconv.of_le (by norm_cast))]
  have h1 : ∀ i, fderiv ℝ (fun y => fderiv ℝ (noyauGreen d ⋆ φ) y (𝐞 i)) x (𝐞 i) =
      ∫ t, noyauGreen d t * fderiv ℝ (fun y => fderiv ℝ φ y (𝐞 i)) (x - t) (𝐞 i) := by
    intro i
    have : (fun y => fderiv ℝ (noyauGreen d ⋆ φ) y (𝐞 i)) =
        noyauGreen d ⋆ fun z => fderiv ℝ φ z (𝐞 i) :=
      funext fun y => fderiv_convolution_apply hd (hφ.of_le (by norm_cast)) hφc y (𝐞 i)
    rw [this, fderiv_convolution_apply hd (hψ _) (hψc _), convolution_def]
    rfl
  simp_rw [h1]
  rw [← integral_finsetSum _ fun i _ => ?_]
  · set φ' : ℝᵈ → ℝ := fun y => φ (x + y)
    have hφ' : ContDiff ℝ 2 φ' := hφ2.comp (contDiff_const.add contDiff_id)
    have hφ'c : HasCompactSupport φ' := hφc.comp_homeomorph (Homeomorph.addLeft x)
    have key := integral_noyauGreen_mul_lapl hd hφ' hφ'c
    have hd1 : ∀ v y, fderiv ℝ φ' y v = fderiv ℝ φ (x + y) v := fun v y => by
      simp only [φ', fderiv_comp_add_left]
    have hd2 : ∀ v w t, fderiv ℝ (fun y => fderiv ℝ φ' y v) t w =
        fderiv ℝ (fun y => fderiv ℝ φ y v) (x + t) w := fun v w t => by
      simp_rw [hd1]
      rw [fderiv_comp_add_left (f := fun y => fderiv ℝ φ y v)]
    simp_rw [hd2] at key
    simp only [φ', add_zero] at key
    rw [← integral_neg_eq_self] at key
    have heven : ∀ t : ℝᵈ, noyauGreen d (-t) = noyauGreen d t := fun t => by
      simp [noyauGreen]
    simp_rw [heven, ← sub_eq_add_neg] at key
    simp_rw [← Finset.mul_sum]
    rw [key, neg_neg]
  · exact hψc _ |>.fderiv_apply (𝕜 := ℝ) (𝐞 i) |>.convolutionExists_right (lsmul ℝ ℝ) hG
      (((hψ _).continuous_fderiv one_ne_zero).clm_apply continuous_const) x

end M1Analyse
