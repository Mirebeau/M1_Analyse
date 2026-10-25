/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.NoyauGreen
import M1Analyse.Sobolev.W1p

/-!
# §5.4 Injections de Sobolev - cas sur-critique (`subsec:injSurCrit`)

Source : `Include/Sobolev.tex`, sous-section `subsec:injSurCrit`. Espaces `W^{1,p}` de
`M1Analyse/Sobolev/W1p.lean`. Non formalisé : `rem:SobSurCritIter` (`W^{s,p}`, `s ≥ 2`).

`prop:convolPow2` : coordonnées polaires (`homeomorphUnitSphereProd`) et, le long de chaque
rayon, `|f(sz) - f(0)| ≤ ∫_0^r |∇f(tz)| dt` (variante simplifiée de la preuve du cours, même
constante `r^d/d`). `eq:normLqPow` : `integral_fun_norm_addHaar`. `th:injSurCrit` : pour
`φ ∈ 𝓓(ℝ^d)`, inégalités de Morrey (`prop:convolPow2`, Hölder, `eq:normLqPow`, moyenne sur la
boule `B((x+y)/2, |x-y|/2)`, resp. `B(x,1)`) ; puis densité de `𝓓(ℝ^d)`
(`prop_testDenseWsp_dense`) : la suite approchante est uniformément de Cauchy, sa limite
uniforme `v` est continue, tend vers `0` à l'infini, et coïncide p.p. avec `u` (sous-suite
convergeant p.p.). `corol:injSurCritOm` : via l'opérateur de prolongement.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal


namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

private theorem injSurCrit_nontrivial (hd : 1 ≤ d) : Nontrivial ℝᵈ :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)

/-- Coordonnées polaires (avec intégrabilité de l'intégrale radiale). -/
private theorem injSurCrit_polaire (hd : 1 ≤ d) {g : ℝᵈ → ℝ} (hg : Integrable g) :
    ∫ y, g y = ∫ z, (∫ r in Ioi (0 : ℝ), r ^ (d - 1) * g (r • (z : ℝᵈ)))
      ∂(volume : Measure ℝᵈ).toSphere ∧
    Integrable (fun z : sphere (0 : ℝᵈ) 1 => ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * g (r • (z : ℝᵈ)))
      (volume : Measure ℝᵈ).toSphere := by
  have := injSurCrit_nontrivial hd
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
  have hz : ∀ z : sphere (0 : ℝᵈ) 1, ∫ r, F (z, r) ∂(Measure.volumeIoiPow (d - 1)) =
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * g (r • (z : ℝᵈ)) := fun z => by
    simp only [Measure.volumeIoiPow, ENNReal.ofReal, hF,
      homeomorphUnitSphereProd_symm_apply_coe]
    rw [integral_withDensity_eq_integral_smul, integral_subtype_comap measurableSet_Ioi
      (fun a ↦ Real.toNNReal (a ^ (d - 1)) • g (a • (z : ℝᵈ)))]
    · refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _), smul_eq_mul]
    · exact (measurable_subtype_coe.pow_const _).real_toNNReal
  refine ⟨?_, (hint.integral_prod_left).congr (Eventually.of_forall hz)⟩
  calc ∫ y, g y = ∫ y : ({0}ᶜ : Set ℝᵈ), g y ∂((volume : Measure ℝᵈ).comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ g x,
          restrict_compl_singleton]
    _ = ∫ p, F p ∂((volume : Measure ℝᵈ).toSphere.prod (Measure.volumeIoiPow (d - 1))) := by
        rw [← hmp.integral_comp (homeomorphUnitSphereProd ℝᵈ).measurableEmbedding]
        simp only [hFe]
    _ = ∫ z, ∫ r, F (z, r) ∂(Measure.volumeIoiPow (d - 1)) ∂(volume : Measure ℝᵈ).toSphere :=
        integral_prod F hint
    _ = _ := by simp only [hz]

/-- `x ↦ |x|^{1-d}` est intégrable sur toute boule `B(0,R)` de `ℝ^d`. -/
private theorem injSurCrit_integrableOn_ball_norm_rpow (hd : 1 ≤ d) (R : ℝ) :
    IntegrableOn (fun y : ℝᵈ => ‖y‖ ^ ((1 : ℝ) - d)) (ball 0 R) := by
  have := injSurCrit_nontrivial hd
  rw [integrableOn_fun_norm_addHaar volume (f := fun r : ℝ => r ^ ((1 : ℝ) - d)),
    finrank_euclideanSpace_fin]
  refine (integrableOn_const (C := (1 : ℝ)) (by simp)).congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  rw [smul_eq_mul, ← Real.rpow_natCast, ← Real.rpow_add hy0, Nat.cast_sub hd]
  simp

/-- Restriction radiale d'une indicatrice de boule. -/
private theorem injSurCrit_radial_indicator {G : ℝᵈ → ℝ} (z : ℝᵈ) (hz : ‖z‖ = 1) (r : ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * (ball (0 : ℝᵈ) r).indicator G (s • z) =
      ∫ s in Ioo 0 r, s ^ (d - 1) * G (s • z) := by
  rw [← Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  have hmem : s • z ∈ ball (0 : ℝᵈ) r ↔ s ∈ Iio r := by
    rw [mem_ball, dist_zero_right, norm_smul, hz, mul_one, Real.norm_of_nonneg hs.le, mem_Iio]
  by_cases h : s ∈ Iio r
  · rw [indicator_of_mem (hmem.2 h), indicator_of_mem h]
  · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), indicator_of_notMem h, mul_zero]

private theorem injSurCrit_norm_fderiv_apply_le {f : ℝᵈ → ℝ} (y z : ℝᵈ) (hz : ‖z‖ = 1) :
    |fderiv ℝ f y z| ≤ ‖gradient f y‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map, ← Real.norm_eq_abs]
  simpa [hz] using (fderiv ℝ f y).le_opNorm z

private theorem injSurCrit_ray (hd : 1 ≤ d) {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 1 f) (x z : ℝᵈ)
    (hz : ‖z‖ = 1) {r : ℝ} (hr : 0 < r) :
    ∫ s in Ioo 0 r, s ^ (d - 1) * |f x - f (x + s • z)| ≤
      r ^ d / d * ∫ s in Ioo 0 r, ‖gradient f (x + s • z)‖ := by
  set B : ℝ → ℝ := fun s => ‖gradient f (x + s • z)‖ with hB
  have hcont : Continuous fun s : ℝ => x + s • z := by fun_prop
  have hBc : Continuous B :=
    (((hf.continuous_fderiv one_ne_zero).comp hcont).norm).congr fun s => by
      simp [hB, gradient]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (x + s • z))
      (fderiv ℝ f (x + t • z) z) t := fun t => by
    have := ((hf.differentiable one_ne_zero) (x + t • z)).hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const z).const_add x)
    simp only [one_smul] at this
    exact this
  have hg'c : Continuous fun t : ℝ => fderiv ℝ f (x + t • z) z :=
    ((hf.continuous_fderiv one_ne_zero).comp hcont).clm_apply continuous_const
  set K := ∫ s in (0 : ℝ)..r, B s with hK
  have hA : ∀ s ∈ Ioo 0 r, |f x - f (x + s • z)| ≤ K := by
    intro s hs
    rw [abs_sub_comm]
    have h1 : f (x + s • z) - f x = ∫ t in (0 : ℝ)..s, fderiv ℝ f (x + t • z) z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hg'c.intervalIntegrable _ _)]
      simp
    rw [h1]
    refine (intervalIntegral.abs_integral_le_integral_abs hs.1.le).trans ?_
    refine (intervalIntegral.integral_mono_on hs.1.le (hg'c.abs.intervalIntegrable _ _)
      (hBc.intervalIntegrable _ _) fun t _ => injSurCrit_norm_fderiv_apply_le _ _ hz).trans ?_
    exact intervalIntegral.integral_mono_interval le_rfl hs.1.le hs.2.le
      (Eventually.of_forall fun t => norm_nonneg _) (hBc.intervalIntegrable _ _)
  have hpow : ∫ s in Ioo 0 r, s ^ (d - 1) = r ^ d / d := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le, integral_pow,
      Nat.sub_add_cancel hd, zero_pow (by omega), sub_zero, Nat.cast_sub hd, Nat.cast_one,
      sub_add_cancel]
  have hKe : ∫ s in Ioo 0 r, B s = K := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le]
  calc ∫ s in Ioo 0 r, s ^ (d - 1) * |f x - f (x + s • z)|
      ≤ ∫ s in Ioo 0 r, s ^ (d - 1) * K := by
        refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo fun s hs => ?_
        · refine ((continuous_pow _).mul ((continuous_const.sub (hf.continuous.comp hcont)).abs)
            |>.integrableOn_Icc).mono_set Ioo_subset_Icc_self
        · exact ((continuous_pow _).mul continuous_const |>.integrableOn_Icc).mono_set
            Ioo_subset_Icc_self
        · exact mul_le_mul_of_nonneg_left (hA s hs) (pow_nonneg hs.1.le _)
    _ = r ^ d / d * ∫ s in Ioo 0 r, B s := by
        rw [integral_mul_const, hpow, hKe]

/-- **Prop. `prop:convolPow2`.** Pour `f ∈ C^1(ℝ^d)`, `x ∈ ℝ^d` et `r > 0`,
`∫_{B(x,r)} |f(x) - f(y)| dy ≤ (r^d/d) ∫_{B(0,r)} ‖∇f(x - y)‖ dy / ‖y‖^{d-1}`.
Preuve (variante simplifiée du cours) : coordonnées polaires et, le long de chaque rayon,
`|f(x + sz) - f(x)| ≤ ∫_0^r ‖∇f(x + tz)‖ dt`, puis `∫_0^r s^{d-1} ds = r^d/d`. -/
theorem prop_convolPow2 {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 1 f) (x : ℝᵈ) {r : ℝ} (hr : 0 < r) :
    ∫ y in ball x r, |f x - f y| ≤
      r ^ d / d * ∫ y in ball (0 : ℝᵈ) r, ‖gradient f (x - y)‖ / ‖y‖ ^ (d - 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have : ∀ y : EuclideanSpace ℝ (Fin 0), y = x := fun y => Subsingleton.elim _ _
    simp [this]
  have := injSurCrit_nontrivial hd
  set F1 : ℝᵈ → ℝ := (ball (0 : ℝᵈ) r).indicator fun y => |f x - f (x + y)| with hF1
  set F2 : ℝᵈ → ℝ := (ball (0 : ℝᵈ) r).indicator
    fun y => ‖gradient f (x + y)‖ / ‖y‖ ^ (d - 1) with hF2
  have hgc : Continuous fun y => ‖gradient f y‖ :=
    ((hf.continuous_fderiv one_ne_zero).norm).congr fun s => by simp [gradient]
  have e1 : ∫ y in ball x r, |f x - f y| = ∫ y, F1 y := by
    rw [← integral_indicator measurableSet_ball,
      ← integral_add_left_eq_self (μ := (volume : Measure ℝᵈ)) _ x]
    congr 1; ext y
    have hmem : x + y ∈ ball x r ↔ y ∈ ball (0 : ℝᵈ) r := by
      simp [mem_ball, dist_eq_norm]
    by_cases h : y ∈ ball (0 : ℝᵈ) r
    · rw [indicator_of_mem (hmem.2 h), hF1, indicator_of_mem h]
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), hF1, indicator_of_notMem h]
  have e2 : ∫ y in ball (0 : ℝᵈ) r, ‖gradient f (x - y)‖ / ‖y‖ ^ (d - 1) = ∫ y, F2 y := by
    rw [← integral_indicator measurableSet_ball, ← integral_neg_eq_self]
    congr 1; ext y
    have hmem : -y ∈ ball (0 : ℝᵈ) r ↔ y ∈ ball (0 : ℝᵈ) r := by simp [mem_ball]
    by_cases h : y ∈ ball (0 : ℝᵈ) r
    · rw [indicator_of_mem (hmem.2 h), hF2, indicator_of_mem h]
      simp [sub_neg_eq_add]
    · rw [indicator_of_notMem (fun h' => h (hmem.1 h')), hF2, indicator_of_notMem h]
  have hi1 : Integrable F1 := by
    refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
    refine ((continuous_const.sub (hf.continuous.comp (continuous_const.add continuous_id))).abs
      |>.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      ball_subset_closedBall
  have hi2 : Integrable F2 := by
    obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn hgc.continuousOn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self hr.le))
    refine IntegrableOn.integrable_indicator ?_ measurableSet_ball
    refine Integrable.mono' ((injSurCrit_integrableOn_ball_norm_rpow hd r).const_mul M) ?_ ?_
    · exact ((hgc.comp (continuous_const.add continuous_id)).measurable.div
        (continuous_norm.pow _).measurable).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_ball]
      refine Eventually.of_forall fun y hy => ?_
      have hxy : x + y ∈ closedBall x r := by
        simpa [mem_closedBall, dist_eq_norm] using (mem_ball_zero_iff.1 hy).le
      have hb := hM _ hxy
      rw [Real.norm_eq_abs, abs_norm] at hb
      rcases eq_or_ne y 0 with rfl | hy0
      · rcases Nat.lt_or_ge 1 d with h1 | h1
        · simpa [zero_pow (by omega : d - 1 ≠ 0)] using
            mul_nonneg hM0 (Real.rpow_nonneg le_rfl _)
        · have : d = 1 := by omega
          subst this
          simp
          simpa using hb
      have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
      rw [norm_div, norm_norm, norm_pow, norm_norm, div_le_iff₀ (by positivity), mul_assoc,
        ← Real.rpow_natCast, ← Real.rpow_add hn, Nat.cast_sub hd]
      simpa using hb
  obtain ⟨p1, i1⟩ := injSurCrit_polaire hd hi1
  obtain ⟨p2, i2⟩ := injSurCrit_polaire hd hi2
  rw [e1, e2, p1, p2, ← integral_const_mul]
  refine integral_mono i1 (i2.const_mul _) fun z => ?_
  have hz : ‖(z : ℝᵈ)‖ = 1 := by simp
  simp only [hF1, hF2]
  rw [injSurCrit_radial_indicator _ hz, injSurCrit_radial_indicator _ hz]
  refine (injSurCrit_ray hd hf x z hz hr).trans_eq ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun s (hs : s ∈ Ioo 0 r) => ?_
  simp only [norm_smul, hz, mul_one, Real.norm_of_nonneg hs.1.le]
  rw [mul_div_cancel₀ _ (pow_ne_zero _ hs.1.ne')]

/-- **Éq. `eq:normLqPow`.** Pour `0 ≤ q` avec `q(d-1) < d` (i.e. `q < d/(d-1)` si `d ≥ 2`) et
`r > 0`, `∫_{B(0,r)} |y|^{-q(d-1)} dy = |𝕊| r^{(d-1)(1-q)+1} / ((d-1)(1-q)+1)`. -/
theorem eq_normLqPow (hd : 1 ≤ d) {q : ℝ} (_hq0 : 0 ≤ q) (hqd : q * (d - 1) < d) {r : ℝ}
    (hr : 0 < r) :
    ∫ y in ball (0 : ℝᵈ) r, (‖y‖ ^ (d - 1 : ℝ))⁻¹ ^ q =
      (volume : Measure ℝᵈ).toSphere.real univ *
        (r ^ ((d - 1) * (1 - q) + 1) / ((d - 1) * (1 - q) + 1)) := by
  have : Nontrivial ℝᵈ :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  set k : ℝ → ℝ := fun s => (s ^ (d - 1 : ℝ))⁻¹ ^ q with hk
  have h1 : ∫ y in ball (0 : ℝᵈ) r, (‖y‖ ^ (d - 1 : ℝ))⁻¹ ^ q =
      ∫ y : ℝᵈ, (Iio r).indicator k ‖y‖ := by
    rw [← integral_indicator measurableSet_ball]
    congr 1; ext y
    by_cases hy : y ∈ ball (0 : ℝᵈ) r
    · rw [indicator_of_mem hy, indicator_of_mem (by simpa using hy)]
    · rw [indicator_of_notMem hy, indicator_of_notMem (by simpa using hy)]
  rw [h1, integral_fun_norm_addHaar, Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin,
    nsmul_eq_mul, smul_eq_mul, mul_assoc]
  congr 2
  have hb : -1 < ((d : ℝ) - 1) * (1 - q) := by nlinarith
  calc ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • (Iio r).indicator k y
      = ∫ y in Ioc (0 : ℝ) r, y ^ (((d : ℝ) - 1) * (1 - q)) := by
        rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
        refine integral_congr_ae ?_
        filter_upwards [(measure_singleton r : volume {r} = 0) |> measure_eq_zero_iff_ae_notMem.1]
          with y hyr
        by_cases hy : y ∈ Ioo (0 : ℝ) r
        · rw [indicator_of_mem (show y ∈ Ioi 0 from hy.1),
            indicator_of_mem (show y ∈ Ioc 0 r from ⟨hy.1, hy.2.le⟩), smul_eq_mul,
            indicator_of_mem (show y ∈ Iio r from hy.2)]
          have hy0 : 0 < y := hy.1
          simp only [hk]
          rw [← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one, ← Real.rpow_neg_one,
            ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
            ← Real.rpow_add hy0]
          congr 1; ring
        · have : y ∉ Ioc (0 : ℝ) r := fun h => hy ⟨h.1, lt_of_le_of_ne h.2 hyr⟩
          rw [indicator_of_notMem this]
          by_cases hy0 : y ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem hy0,
              indicator_of_notMem (show y ∉ Iio r from fun h => hy ⟨hy0, h⟩), smul_zero]
          · rw [indicator_of_notMem hy0]
    _ = _ := by
        rw [← intervalIntegral.integral_of_le hr.le, integral_rpow (Or.inl hb),
          Real.zero_rpow (by linarith), sub_zero]

private theorem injSurCrit_norm_gradient_eq (f : ℝᵈ → ℝ) (y : ℝᵈ) :
    ‖gradient f y‖ = ‖fderiv ℝ f y‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

private theorem injSurCrit_hasCompactSupport_grad {f : ℝᵈ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport fun y => ‖gradient f y‖ := by
  simp_rw [injSurCrit_norm_gradient_eq]
  exact (hfc.fderiv (𝕜 := ℝ)).norm

private theorem injSurCrit_continuous_grad {f : ℝᵈ → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous fun y => ‖gradient f y‖ := by
  simp_rw [injSurCrit_norm_gradient_eq]
  exact (hf.continuous_fderiv one_ne_zero).norm

/-- `|y|^{-(d-1)q}` est intégrable sur les boules si `q(d-1) < d`. -/
private theorem injSurCrit_integrableOn_pow (hd : 1 ≤ d) {q : ℝ} (hqd : q * (d - 1) < d)
    (r : ℝ) :
    IntegrableOn (fun y : ℝᵈ => (‖y‖ ^ (d - 1 : ℝ))⁻¹ ^ q) (ball 0 r) := by
  have := injSurCrit_nontrivial hd
  rw [integrableOn_fun_norm_addHaar volume (f := fun s : ℝ => (s ^ (d - 1 : ℝ))⁻¹ ^ q),
    finrank_euclideanSpace_fin]
  have hb : -1 < ((d : ℝ) - 1) * (1 - q) := by nlinarith
  rcases le_or_gt r 0 with hr | hr
  · rw [Ioo_eq_empty (not_lt.2 hr)]; exact integrableOn_empty
  refine (((intervalIntegral.intervalIntegrable_rpow' hb (a := 0) (b := r)).1).mono_set
    Ioo_subset_Ioc_self).congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy0 : 0 < y := hy.1
  rw [smul_eq_mul, ← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one, ← Real.rpow_neg_one,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity), ← Real.rpow_add hy0]
  ring_nf

/-- Oscillation sur une boule (preuve de `th:injSurCrit`, via `prop:convolPow2`, Hölder et
`eq:normLqPow`). -/
private theorem injSurCrit_osc (hd : 1 ≤ d) {P : ℝ} (hP : (d : ℝ) < P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝᵈ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f → ∀ (x : ℝᵈ) (r : ℝ),
      0 < r → ∫ y in ball x r, |f x - f y| ≤
        r ^ d * K * r ^ (1 - d / P) * (∫ y, ‖gradient f y‖ ^ P) ^ (1 / P) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hP1 : 1 < P := by linarith
  set q := P / (P - 1) with hq
  have hpq : P.HolderConjugate q := Real.HolderConjugate.conjExponent hP1
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  have hqd : q * (d - 1) < d := by
    rw [hq, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith
  set a := ((d : ℝ) - 1) * (1 - q) + 1 with ha
  have ha0 : 0 < a := by rw [ha]; nlinarith
  have haq : a * (1 / q) = 1 - d / P := by
    have hP0 : P - 1 ≠ 0 := by linarith
    have hP0' : P ≠ 0 := by linarith
    rw [ha, hq]; field_simp; ring
  set σ := (volume : Measure ℝᵈ).toSphere.real univ
  have hσ : 0 ≤ σ := measureReal_nonneg
  refine ⟨1 / d * (σ / a) ^ (1 / q), by positivity, fun f hf hfc x r hr => ?_⟩
  set G : ℝᵈ → ℝ := fun y => ‖gradient f y‖ with hG
  have hGc : Continuous G := injSurCrit_continuous_grad hf
  have hGs : HasCompactSupport G := injSurCrit_hasCompactSupport_grad hfc
  have hGx : Continuous fun y => G (x - y) := hGc.comp (continuous_const.sub continuous_id)
  have hGxs : HasCompactSupport fun y => G (x - y) := hGs.comp_homeomorph (Homeomorph.subLeft x)
  set μ := (volume : Measure ℝᵈ).restrict (ball 0 r)
  have h1 := prop_convolPow2 hf x hr
  have e1 : ∫ y in ball (0 : ℝᵈ) r, ‖gradient f (x - y)‖ / ‖y‖ ^ (d - 1) =
      ∫ y, G (x - y) * (‖y‖ ^ (d - 1 : ℝ))⁻¹ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [div_eq_mul_inv, ← Real.rpow_natCast, Nat.cast_sub hd, Nat.cast_one]
  have hmem1 : MemLp (fun y => G (x - y)) (ENNReal.ofReal P) μ :=
    (hGx.memLp_of_hasCompactSupport hGxs).restrict _
  have hmem2 : MemLp (fun y : ℝᵈ => (‖y‖ ^ (d - 1 : ℝ))⁻¹) (ENNReal.ofReal q) μ := by
    have hint := injSurCrit_integrableOn_pow (d := d) hd hqd r
    rw [← integrable_norm_rpow_iff _ (by simpa using hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le]
    · refine hint.congr (Eventually.of_forall fun y => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
    · exact ((continuous_norm.rpow_const fun _ => Or.inr (by linarith)).measurable.inv
        ).aestronglyMeasurable
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun y => norm_nonneg _)
    (Eventually.of_forall fun y => by positivity) hmem1 hmem2
  have hGp : Integrable fun y => G y ^ P :=
    (hGc.rpow_const fun _ => Or.inr (by linarith)).integrable_of_hasCompactSupport
      (hGs.rpow_const (by linarith))
  have h2 : ∫ y, G (x - y) ^ P ∂μ ≤ ∫ y, G y ^ P := by
    rw [← integral_sub_left_eq_self (μ := (volume : Measure ℝᵈ)) _ x]
    refine setIntegral_le_integral ?_ (Eventually.of_forall fun y => by positivity)
    exact (hGp.comp_sub_left x)
  have h3 : ∫ y, ((‖y‖ ^ (d - 1 : ℝ))⁻¹) ^ q ∂μ = σ * (r ^ a / a) :=
    eq_normLqPow hd hq0.le hqd hr
  have h4 : (σ * (r ^ a / a)) ^ (1 / q) = (σ / a) ^ (1 / q) * r ^ (1 - d / P) := by
    rw [← haq, Real.rpow_mul hr.le, mul_div_assoc', mul_div_right_comm,
      Real.mul_rpow (by positivity) (by positivity)]
  rw [h3, h4] at hH
  have hint0 : 0 ≤ ∫ y, G (x - y) ^ P ∂μ := integral_nonneg fun y => by positivity
  have h5 : (∫ y, G (x - y) ^ P ∂μ) ^ (1 / P) ≤ (∫ y, G y ^ P) ^ (1 / P) :=
    Real.rpow_le_rpow hint0 h2 (by positivity)
  rw [e1] at h1
  have hr0 : 0 ≤ r ^ d / d := by positivity
  calc ∫ y in ball x r, |f x - f y| ≤ r ^ d / d * ∫ y, G (x - y) * (‖y‖ ^ (d - 1 : ℝ))⁻¹ ∂μ :=
        h1
    _ ≤ r ^ d / d * ((∫ y, G y ^ P) ^ (1 / P) * ((σ / a) ^ (1 / q) * r ^ (1 - d / P))) := by
        refine mul_le_mul_of_nonneg_left (hH.trans ?_) hr0
        exact mul_le_mul_of_nonneg_right h5 (by positivity)
    _ = _ := by ring

private theorem injSurCrit_intBall {g : ℝᵈ → ℝ} (hg : Continuous g) (x : ℝᵈ) (s : ℝ) :
    IntegrableOn g (ball x s) :=
  (hg.continuousOn.integrableOn_compact (isCompact_closedBall x s)).mono_set
    ball_subset_closedBall

private theorem injSurCrit_vol_ball (x : ℝᵈ) {s : ℝ} (hs : 0 < s) :
    (volume : Measure ℝᵈ).real (ball x s) = s ^ d * (volume : Measure ℝᵈ).real (ball 0 1) := by
  rw [measureReal_def, Measure.addHaar_ball_of_pos _ _ hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), finrank_euclideanSpace_fin]
  rfl

private theorem injSurCrit_vol_pos (hd : 1 ≤ d) :
    0 < (volume : Measure ℝᵈ).real (ball (0 : ℝᵈ) 1) := by
  have := injSurCrit_nontrivial hd
  exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

/-- Inégalité de Morrey (partie Hölder) pour `f ∈ C¹_c(ℝ^d)`. -/
private theorem injSurCrit_holderFun (hd : 1 ≤ d) {P : ℝ} (hP : (d : ℝ) < P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : ℝᵈ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f → ∀ x y : ℝᵈ,
      |f x - f y| ≤ K * dist x y ^ (1 - d / P) * (∫ y, ‖gradient f y‖ ^ P) ^ (1 / P) := by
  obtain ⟨K0, hK0, hosc⟩ := injSurCrit_osc hd hP
  set ω := (volume : Measure ℝᵈ).real (ball (0 : ℝᵈ) 1)
  have hω : 0 < ω := injSurCrit_vol_pos hd
  have hω0 : ω ≠ 0 := hω.ne'
  refine ⟨2 ^ (d + 1) * K0 / ω, by positivity, fun f hf hfc x y => ?_⟩
  set N := (∫ y, ‖gradient f y‖ ^ P) ^ (1 / P)
  have hN : 0 ≤ N := Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, abs_zero]
    positivity
  set r := dist x y
  have hr : 0 < r := dist_pos.2 hxy
  set m := midpoint ℝ x y
  have hBx : ball m (r / 2) ⊆ ball x r := ball_subset_ball' (by
    rw [dist_comm, dist_left_midpoint (𝕜 := ℝ)]; simp [r]; linarith)
  have hBy : ball m (r / 2) ⊆ ball y r := ball_subset_ball' (by
    rw [dist_comm, dist_right_midpoint (𝕜 := ℝ)]; simp [r]; linarith)
  have hcf := hf.continuous
  have hcx : Continuous fun z => |f x - f z| := (continuous_const.sub hcf).abs
  have hcy : Continuous fun z => |f y - f z| := (continuous_const.sub hcf).abs
  have h1 : ∫ z in ball m (r / 2), |f x - f y| ≤
      ∫ z in ball m (r / 2), (|f x - f z| + |f y - f z|) := by
    refine setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne)
      ((injSurCrit_intBall hcx _ _).add (injSurCrit_intBall hcy _ _)) measurableSet_ball
      fun z _ => ?_
    calc |f x - f y| = |(f x - f z) - (f y - f z)| := by ring_nf
      _ ≤ _ := abs_sub _ _
  rw [integral_add (injSurCrit_intBall hcx _ _) (injSurCrit_intBall hcy _ _),
    setIntegral_const, smul_eq_mul, injSurCrit_vol_ball m (by linarith)] at h1
  have h2 := setIntegral_mono_set (injSurCrit_intBall hcx x r)
    (Eventually.of_forall fun z => abs_nonneg _) (Eventually.of_forall hBx)
  have h3 := setIntegral_mono_set (injSurCrit_intBall hcy y r)
    (Eventually.of_forall fun z => abs_nonneg _) (Eventually.of_forall hBy)
  have h4 := hosc f hf hfc x r hr
  have h5 := hosc f hf hfc y r hr
  have hrd : 0 < r ^ d := by positivity
  have key : (r / 2) ^ d * ω * |f x - f y| ≤ 2 * (r ^ d * K0 * r ^ (1 - d / P) * N) := by
    linarith
  have h2d : (r / 2) ^ d = r ^ d / 2 ^ d := div_pow _ _ _
  rw [h2d] at key
  have hpos : 0 < r ^ d / 2 ^ d * ω := by positivity
  refine le_of_mul_le_mul_left (key.trans_eq ?_) hpos
  field_simp
  ring

/-- Inégalité de Morrey (borne uniforme) pour `f ∈ C¹_c(ℝ^d)`. -/
private theorem injSurCrit_boundFun (hd : 1 ≤ d) {P : ℝ} (hP : (d : ℝ) < P) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ f : ℝᵈ → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      ∀ x : ℝᵈ, |f x| ≤ K1 * (∫ y, ‖gradient f y‖ ^ P) ^ (1 / P) +
        K2 * (∫ y, |f y| ^ P) ^ (1 / P) := by
  obtain ⟨K0, hK0, hosc⟩ := injSurCrit_osc hd hP
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hP1 : 1 < P := by linarith
  set q := P / (P - 1) with hq
  have hpq : P.HolderConjugate q := Real.HolderConjugate.conjExponent hP1
  have hq0 : 0 < q := div_pos (by linarith) (by linarith)
  set ω := (volume : Measure ℝᵈ).real (ball (0 : ℝᵈ) 1)
  have hω : 0 < ω := injSurCrit_vol_pos hd
  have hω0 : ω ≠ 0 := hω.ne'
  refine ⟨K0 / ω, ω ^ (1 / q) / ω, by positivity, by positivity, fun f hf hfc x => ?_⟩
  set N := (∫ y, ‖gradient f y‖ ^ P) ^ (1 / P)
  set M := (∫ y, |f y| ^ P) ^ (1 / P)
  have hcf := hf.continuous
  have hcx : Continuous fun z => |f x - f z| := (continuous_const.sub hcf).abs
  have h1 : ∫ z in ball x 1, |f x| ≤ ∫ z in ball x 1, (|f x - f z| + |f z|) := by
    refine setIntegral_mono_on (integrableOn_const measure_ball_lt_top.ne)
      ((injSurCrit_intBall hcx _ _).add (injSurCrit_intBall hcf.abs _ _)) measurableSet_ball
      fun z _ => ?_
    calc |f x| = |(f x - f z) + f z| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  rw [integral_add (injSurCrit_intBall hcx _ _) (injSurCrit_intBall hcf.abs _ _),
    setIntegral_const, smul_eq_mul, injSurCrit_vol_ball x one_pos, one_pow, one_mul] at h1
  have h4 := hosc f hf hfc x 1 one_pos
  rw [one_pow, one_mul, Real.one_rpow, mul_one] at h4
  -- Hölder sur `B(x,1)`
  set μ := (volume : Measure ℝᵈ).restrict (ball x 1)
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmem1 : MemLp (fun y => |f y|) (ENNReal.ofReal P) μ :=
    (hcf.abs.memLp_of_hasCompactSupport hfc.abs).restrict _
  have hmem2 : MemLp (fun _ : ℝᵈ => (1 : ℝ)) (ENNReal.ofReal q) μ := memLp_const _
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun y => abs_nonneg _)
    (Eventually.of_forall fun y => zero_le_one) hmem1 hmem2
  simp only [mul_one, Real.one_rpow, integral_const, smul_eq_mul] at hH
  rw [measureReal_restrict_apply_univ, injSurCrit_vol_ball x one_pos, one_pow,
    one_mul] at hH
  have hfp : Integrable fun y => |f y| ^ P :=
    (hcf.abs.rpow_const fun _ => Or.inr (by linarith)).integrable_of_hasCompactSupport
      (hfc.abs.rpow_const (by linarith))
  have h2 : ∫ y, |f y| ^ P ∂μ ≤ ∫ y, |f y| ^ P :=
    setIntegral_le_integral hfp (Eventually.of_forall fun y => by positivity)
  have h5 : (∫ y, |f y| ^ P ∂μ) ^ (1 / P) ≤ M :=
    Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) h2 (by positivity)
  have hH' : ∫ z in ball x 1, |f z| ≤ M * ω ^ (1 / q) :=
    hH.trans (mul_le_mul_of_nonneg_right h5 (by positivity))
  have key : ω * |f x| ≤ K0 * N + M * ω ^ (1 / q) := by linarith
  refine le_of_mul_le_mul_left (key.trans_eq ?_) hω
  field_simp

/-- `‖f‖_p` pour `f` continue à support compact. -/
private theorem injSurCrit_eLpNorm_eq {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) {g : ℝᵈ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    (eLpNorm g p volume).toReal = (∫ y, |g y| ^ p.toReal) ^ (1 / p.toReal) := by
  rw [(hg.memLp_of_hasCompactSupport hgc).eLpNorm_eq_integral_rpow_norm hp0 hp,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _),
    one_div]
  rfl

private theorem injSurCrit_restrict_top :
    (volume : Measure ℝᵈ).restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ) = volume := by
  simp

/-- `|∇f| ≤ ∑ᵢ |∂ᵢ f|`. -/
private theorem injSurCrit_norm_gradient_le (f : ℝᵈ → ℝ) (y : ℝᵈ) :
    ‖gradient f y‖ ≤ ∑ i, |fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))| := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  conv_lhs => rw [← b.sum_repr' (gradient f y)]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, gradient, real_inner_comm,
    InnerProductSpace.toDual_symm_apply, EuclideanSpace.basisFun_apply]

open scoped Distributions in
/-- Inégalités de Morrey pour les fonctions test, en termes des normes de `W^{1,p}`. -/
private theorem injSurCrit_test (hd : 1 ≤ d) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞) :
    ∃ C C' : ℝ, 0 ≤ C ∧ 0 ≤ C' ∧ ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ),
      (∀ x, |φ x| ≤ C * ‖testGrad ⊤ p φ‖) ∧
      ∀ x y, |φ x - φ y| ≤
        C' * dist x y ^ (1 - d / p.toReal) * ‖(testGrad ⊤ p φ).snd‖ := by
  have hp1 : 1 ≤ p := Fact.out
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp1).ne'
  have hP : (d : ℝ) < p.toReal := by
    have := (ENNReal.toReal_lt_toReal (by simp) hp).2 hdp
    simpa using this
  obtain ⟨K, hK, hhol⟩ := injSurCrit_holderFun hd hP
  obtain ⟨K1, K2, hK1, hK2, hbd⟩ := injSurCrit_boundFun hd hP
  refine ⟨K1 * d + K2, K * d, by positivity, by positivity, fun φ => ?_⟩
  set T := testGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p φ
  have hf : ContDiff ℝ 1 (φ : ℝᵈ → ℝ) := φ.contDiff.of_le (by exact_mod_cast le_top)
  have hfc : HasCompactSupport (φ : ℝᵈ → ℝ) := φ.hasCompactSupport
  set e : Fin d → ℝᵈ := fun i => EuclideanSpace.single i (1 : ℝ)
  have hpart : ∀ i, Continuous fun y => fderiv ℝ φ y (e i) := fun i =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpartc : ∀ i, HasCompactSupport fun y => fderiv ℝ φ y (e i) := fun i =>
    hfc.fderiv_apply (𝕜 := ℝ) (e i)
  -- normes
  have hM : (∫ y, |φ y| ^ p.toReal) ^ (1 / p.toReal) = ‖T.fst‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (testGrad_fst ⊤ p φ), injSurCrit_restrict_top,
      injSurCrit_eLpNorm_eq hp0 hp hf.continuous hfc]
  have hNi : ∀ i, (eLpNorm (fun y => fderiv ℝ φ y (e i)) p volume).toReal = ‖T.snd i‖ := by
    intro i
    rw [Lp.norm_def, eLpNorm_congr_ae (testGrad_snd ⊤ p φ i), injSurCrit_restrict_top]
  have hN : (∫ y, ‖gradient φ y‖ ^ p.toReal) ^ (1 / p.toReal) ≤ d * ‖T.snd‖ := by
    have h1 : (∫ y, ‖gradient φ y‖ ^ p.toReal) ^ (1 / p.toReal) =
        (eLpNorm (fun y => ‖gradient φ y‖) p volume).toReal := by
      rw [injSurCrit_eLpNorm_eq hp0 hp (injSurCrit_continuous_grad hf)
        (injSurCrit_hasCompactSupport_grad hfc)]
      simp only [abs_norm]
    have hfin : ∀ i, eLpNorm (fun y => fderiv ℝ φ y (e i)) p volume ≠ ∞ := fun i =>
      ((hpart i).memLp_of_hasCompactSupport (hpartc i)).eLpNorm_ne_top
    have h2 : eLpNorm (fun y => ‖gradient φ y‖) p volume ≤
        ∑ i, eLpNorm (fun y => fderiv ℝ φ y (e i)) p volume := by
      refine (eLpNorm_mono_real (g := ∑ i, fun y => |fderiv ℝ φ y (e i)|)
        (injSurCrit_continuous_grad hf).aestronglyMeasurable fun y => ?_).trans
        ((eLpNorm_sum_le hp1).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)))
      · rw [Real.norm_eq_abs, abs_norm, Finset.sum_apply]
        exact injSurCrit_norm_gradient_le _ y
      · exact eLpNorm_norm _ (hpart i).aestronglyMeasurable
    rw [h1]
    refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => hfin i) h2).trans ?_
    rw [ENNReal.toReal_sum fun i _ => hfin i]
    simp_rw [hNi]
    calc ∑ i, ‖T.snd i‖ ≤ ∑ _i : Fin d, ‖T.snd‖ :=
          Finset.sum_le_sum fun i _ => PiLp.norm_apply_le _ i
      _ = d * ‖T.snd‖ := by simp
  have hsnd : ‖T.snd‖ ≤ ‖T‖ := WithLp.norm_snd_le _ T
  have hfst : ‖T.fst‖ ≤ ‖T‖ := WithLp.norm_fst_le _ T
  refine ⟨fun x => ?_, fun x y => ?_⟩
  · refine (hbd _ hf hfc x).trans ?_
    rw [hM]
    have h1 := mul_le_mul_of_nonneg_left (hN.trans (mul_le_mul_of_nonneg_left hsnd
      (Nat.cast_nonneg d))) hK1
    have h2 := mul_le_mul_of_nonneg_left hfst hK2
    nlinarith
  · refine (hhol _ hf hfc x y).trans ?_
    have hα : 0 ≤ dist x y ^ (1 - d / p.toReal) := Real.rpow_nonneg dist_nonneg _
    calc K * dist x y ^ (1 - d / p.toReal) * (∫ y, ‖gradient φ y‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤ K * dist x y ^ (1 - d / p.toReal) * (d * ‖T.snd‖) :=
          mul_le_mul_of_nonneg_left hN (by positivity)
      _ = _ := by ring

private theorem injSurCrit_lt_of_le {a b C ε : ℝ} (hC : 0 ≤ C) (hb : 0 ≤ b)
    (h1 : a ≤ C * b) (h2 : b < ε / (C + 1)) : a < ε := by
  have hC1 : 0 < C + 1 := by linarith
  rw [lt_div_iff₀ hC1] at h2
  nlinarith

/-- **Th. `th:injSurCrit` (Injection sur-critique `W^{1,p} ⊂ C^{1-d/p}_0`, inégalité de Morrey).**
Pour `p ∈ ]d, ∞[`, toute `u ∈ W^{1,p}(ℝ^d)` admet un représentant continu `v` avec
`‖v‖_∞ ≤ C ‖u‖_{W^{1,p}}`, `|v(x) - v(y)| ≤ C' |x - y|^α ‖∇u‖_p` (`α = 1 - d/p`, `‖∇u‖_p` norme de
`∇u` dans `L^p(ℝ^d)^d`), et `v(x) → 0` quand `|x| → ∞` ; `C, C'` ne dépendent que de `p, d`.
Preuve : inégalités du cours pour les fonctions test ; puis (différent du cours) la suite de
fonctions test approchant `u` est uniformément de Cauchy, sa limite uniforme `v` est continue et
tend vers `0` à l'infini (limite uniforme de fonctions à support compact). -/
theorem th_injSurCrit (hd : 1 ≤ d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p)
    (hp : p ≠ ∞) :
    ∃ C C' : ℝ, ∀ u : Sobolev1 (⊤ : TopologicalSpace.Opens ℝᵈ) p, ∃ v : ℝᵈ → ℝ, Continuous v ∧
      (u.val : ℝᵈ → ℝ) =ᵐ[volume] v ∧
      (∀ x, |v x| ≤ C * ‖u‖) ∧
      (∀ x y, |v x - v y| ≤ C' * dist x y ^ (1 - d / p.toReal) * ‖u.gradL‖) ∧
      Tendsto v (cocompact ℝᵈ) (𝓝 0) := by
  obtain ⟨C, C', hC, hC', hT⟩ := injSurCrit_test hd hdp hp
  refine ⟨C, C', fun u => ?_⟩
  simp only [Sobolev1.val_def, Sobolev1.gradL_def]
  set U : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p := u.1 with hUdef
  have hu : U ∈ W1p0 (⊤ : TopologicalSpace.Opens ℝᵈ) p := by
    rw [prop_testDenseWsp_dense hp]; exact u.2
  rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hu
  obtain ⟨w, hw, hlim⟩ := mem_closure_iff_seq_limit.1 hu
  choose φ hφ using hw
  set T := fun n => testGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p (φ n) with hTdef
  have hTw : T = w := funext hφ
  have hTlim : Tendsto T atTop (𝓝 U) := by rw [hTw]; exact hlim
  -- estimation clé : `|φₙ x - φₘ x| ≤ C ‖Tₙ - Tₘ‖`
  have hdiff : ∀ n m x, |φ n x - φ m x| ≤ C * ‖T n - T m‖ := fun n m x => by
    have := (hT (φ n - φ m)).1 x
    rwa [map_sub] at this
  have hTU : Tendsto (fun n => ‖T n - U‖) atTop (𝓝 0) := by
    have := (hTlim.sub_const U).norm
    simpa using this
  -- convergence ponctuelle
  have hcauchy : ∀ x, CauchySeq fun n => φ n x := fun x => by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hδ : 0 < ε / (C + 1) / 2 := by
      have : 0 < C + 1 := by linarith
      positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hTU).2 _ hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have h1 : ‖T n - T N‖ ≤ ‖T n - U‖ + ‖T N - U‖ := by
      rw [← norm_neg (T N - U), neg_sub]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖T n - U‖ + ‖T N - U‖ < ε / (C + 1) := by
      linarith [hN n hn, hN N le_rfl]
    exact injSurCrit_lt_of_le hC (add_nonneg (norm_nonneg _) (norm_nonneg _))
      ((hdiff n N x).trans (mul_le_mul_of_nonneg_left h1 hC)) h2
  obtain ⟨v, hvlim⟩ : ∃ v : ℝᵈ → ℝ, ∀ x, Tendsto (fun n => φ n x) atTop (𝓝 (v x)) :=
    ⟨fun x => limUnder atTop fun n => φ n x, fun x => (hcauchy x).tendsto_limUnder⟩
  -- convergence uniforme
  have hunif_bd : ∀ n x, |φ n x - v x| ≤ C * ‖T n - U‖ := fun n x => by
    refine le_of_tendsto_of_tendsto' (((hvlim x).const_sub (φ n x)).abs)
      ((((tendsto_const_nhds (x := T n)).sub hTlim).norm).const_mul C) fun m => hdiff n m x
  have hunif : TendstoUniformly (fun n => (φ n : ℝᵈ → ℝ)) v atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(tendsto_order.1 hTU).2 (ε / (C + 1)) (by positivity)] with n hn x
    rw [dist_comm, Real.dist_eq]
    exact injSurCrit_lt_of_le hC (norm_nonneg _) (hunif_bd n x) hn
  refine ⟨v, ?_, ?_, ?_, ?_, ?_⟩
  · exact hunif.continuous (Frequently.of_forall fun n => (φ n).continuous)
  · -- égalité presque partout : sous-suite convergeant p.p.
    have hfst : Tendsto (fun n => (T n).fst) atTop (𝓝 U.fst) :=
      ((WithLp.continuous_fst _ _ _).tendsto U).comp hTlim
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hfst).exists_seq_tendsto_ae
    have hae2 : ∀ᵐ x ∂(volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)),
        ∀ n, ((T n).fst : ℝᵈ → ℝ) x = φ n x :=
      ae_all_iff.2 fun n => testGrad_fst ⊤ p (φ n)
    have key : ∀ᵐ x ∂(volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)),
        (U.fst : ℝᵈ → ℝ) x = v x := by
      filter_upwards [hae, hae2] with x hx hx2
      simp only [hx2] at hx
      exact tendsto_nhds_unique hx ((hvlim x).comp hns.tendsto_atTop)
    rw [ae_restrict_iff' (by simp)] at key
    filter_upwards [key] with x hx using hx (by simp)
  · intro x
    refine le_of_tendsto_of_tendsto' (hvlim x).abs (hTlim.norm.const_mul C) fun n => ?_
    exact (hT (φ n)).1 x
  · intro x y
    have hsnd : Tendsto (fun n => ‖(T n).snd‖) atTop (𝓝 ‖U.snd‖) :=
      (((WithLp.continuous_snd _ _ _).tendsto U).comp hTlim).norm
    refine le_of_tendsto_of_tendsto' ((hvlim x).sub (hvlim y)).abs
      (hsnd.const_mul _) fun n => ?_
    exact (hT (φ n)).2 x y
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.1 hunif (ε / 2) (by positivity)).exists
    have hK := (φ n).hasCompactSupport
    filter_upwards [hK.isCompact.compl_mem_cocompact] with x hx
    have h0 : φ n x = 0 := image_eq_zero_of_notMem_tsupport hx
    have := hn x
    rw [h0, dist_comm] at this
    rw [dist_comm]
    linarith

/-- **Cor. `corol:injSurCritOm`.** Si `Ω` a la propriété de prolongement de Sobolev pour
`p ∈ ]d, ∞[` (au lieu de « `Ω` régulier », \claudereport), toute `u ∈ W^{1,p}(Ω)` admet un
représentant continu sur `Ω` avec `‖v‖_{∞,Ω} ≤ C ‖u‖_{W^{1,p}}` et
`|v(x) - v(y)| ≤ C' |x - y|^{1-d/p} ‖u‖_{W^{1,p}}` sur `Ω`. Preuve : `th_injSurCrit` appliqué à
`P u`. -/
theorem corol_injSurCritOm (Ω : TopologicalSpace.Opens ℝᵈ) (hd : 1 ≤ d) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞) (hP : ProlongementSobolev Ω p) :
    ∃ C C' : ℝ, ∀ u : Sobolev1 Ω p, ∃ v : ℝᵈ → ℝ, ContinuousOn v Ω ∧
      (u.val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] v ∧
      (∀ x ∈ (Ω : Set ℝᵈ), |v x| ≤ C * ‖u‖) ∧
      (∀ x ∈ (Ω : Set ℝᵈ), ∀ y ∈ (Ω : Set ℝᵈ),
        |v x - v y| ≤ C' * dist x y ^ (1 - d / p.toReal) * ‖u‖) := by
  obtain ⟨C, C', hT⟩ := th_injSurCrit hd hdp hp
  obtain ⟨P, hPu⟩ := hP
  refine ⟨max C 0 * ‖P‖, max C' 0 * ‖P‖, fun u => ?_⟩
  obtain ⟨v, hvc, hvae, hvb, hvh, -⟩ := hT (P u)
  refine ⟨v, hvc.continuousOn, (hPu u).symm.trans (ae_restrict_of_ae hvae), fun x _ => ?_,
    fun x _ y _ => ?_⟩
  · calc |v x| ≤ C * ‖P u‖ := hvb x
      _ ≤ max C 0 * ‖P u‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      _ ≤ max C 0 * (‖P‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_left (P.le_opNorm u) (le_max_right _ _)
      _ = _ := by ring
  · have hα : 0 ≤ dist x y ^ (1 - d / p.toReal) := Real.rpow_nonneg dist_nonneg _
    have hs : ‖(P u).gradL‖ ≤ ‖P‖ * ‖u‖ :=
      (WithLp.norm_snd_le _ _).trans (P.le_opNorm u)
    calc |v x - v y| ≤ C' * dist x y ^ (1 - d / p.toReal) * ‖(P u).gradL‖ := hvh x y
      _ ≤ max C' 0 * dist x y ^ (1 - d / p.toReal) * (‖P‖ * ‖u‖) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hα) hs
            (norm_nonneg _) (mul_nonneg (le_max_right _ _) hα)
      _ = _ := by ring

end M1Analyse
