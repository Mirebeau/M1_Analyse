/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.RellichCorollaire
import M1Analyse.Dualite.CompaciteFaible
import M1Analyse.Compacite.OperateursCompacts

/-!
# §5.5 Minimisation d'une fonctionnelle non-linéaire sur `H¹(Ω)` (`ex:nonLinMinH1`)

Source : `Include/Sobolev.tex`, `ex:nonLinMinH1`. Hypothèse sur `Ω` : borné et
`ProlongementSobolevTout Ω` (au lieu de « borné régulier », \claudereport), comme pour
`th:Rellich`. Deux preuves : `ex_nonLinMinH1` (directe, celle du cours, via `corol:Rellich`) et
`ex_nonLinMinH1'` (via le second point de `corol:minFctCvxRefl`, dont les hypothèses sont
vérifiées par `ex_nonLinMinH1_hypMinFctCvxRefl`, comme suggéré en fin de preuve du cours).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Fonctionnelle de `ex:nonLinMinH1` :
`J(u) = ∫_Ω (½ |∇u|² + ½ u² - f u + F(u))`. (Pour `u ∈ H¹(Ω)`, `Ω` borné et `F` bornée
mesurable, l'intégrande est intégrable.) -/
noncomputable def fonctionnelleNonLin (Ω : TopologicalSpace.Opens ℝᵈ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) (F : ℝ → ℝ) (u : H1 Ω) : ℝ :=
  ∫ x in (Ω : Set ℝᵈ), ((1 / 2) * ∑ i, u.grad i x ^ 2 + (1 / 2) * u.val x ^ 2 -
    f x * u.val x + F (u.val x))

/-- Un espace de Hilbert réel est réflexif (représentation de Riesz). -/
private lemma nonLinMinH1_reflexif {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] : Reflexif E := by
  rw [def_reflexif_iff_surjective]
  intro Φ
  refine ⟨(InnerProductSpace.toDual ℝ E).symm
    (Φ.comp (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap), ?_⟩
  ext φ
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective φ
  rw [def_reflexif_eval, InnerProductSpace.toDual_apply_apply, real_inner_comm,
    ← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Version pour un sous-espace fermé (évite des unifications d'instances coûteuses). -/
private lemma nonLinMinH1_reflexif_sub {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [CompleteSpace K] : Reflexif K :=
  nonLinMinH1_reflexif

private lemma nonLinMinH1_norm_sq {Ω : TopologicalSpace.Opens ℝᵈ} (u : H1 Ω) :
    ‖u‖ ^ 2 = ‖u.val‖ ^ 2 + ∑ i, ‖u.grad i‖ ^ 2 := by
  have h := norm_W1p (p := 2) (by norm_num) u
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

private lemma nonLinMinH1_norm_val_le {Ω : TopologicalSpace.Opens ℝᵈ} (u : H1 Ω) :
    ‖u.val‖ ≤ ‖u‖ := by
  have h := nonLinMinH1_norm_sq u
  have : 0 ≤ ∑ i, ‖u.grad i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)

private noncomputable def nonLinMinH1_val (Ω : TopologicalSpace.Opens ℝᵈ) :
    H1 Ω →L[ℝ] Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)) :=
  LinearMap.mkContinuous
    { toFun := fun u => u.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun u => by rw [one_mul]; exact nonLinMinH1_norm_val_le u)

private lemma nonLinMinH1_val_apply {Ω : TopologicalSpace.Opens ℝᵈ} (u : H1 Ω) :
    nonLinMinH1_val Ω u = u.val := rfl

private lemma nonLinMinH1_norm_sq_int {Ω : TopologicalSpace.Opens ℝᵈ} (u : H1 Ω) :
    ‖u‖ ^ 2 = (∫ x in (Ω : Set ℝᵈ), u.val x * u.val x) +
      ∑ i, ∫ x in (Ω : Set ℝᵈ), u.grad i x * u.grad i x := by
  rw [← real_inner_self_eq_norm_sq, prop_SobolevBanach_inner]

private lemma nonLinMinH1_integral_mul {Ω : TopologicalSpace.Opens ℝᵈ}
    (f v : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∫ x in (Ω : Set ℝᵈ), f x * v x = inner ℝ f v := by
  simp only [L2.inner_def, Real.inner_apply]


private lemma nonLinMinH1_L1_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] (v w : Lp ℝ 2 μ) :
    ∫ x, |v x - w x| ∂μ ≤ ‖v - w‖ * (μ univ).toReal ^ (1 / 2 : ℝ) := by
  have hm : AEStronglyMeasurable (fun x => v x - w x) μ :=
    (Lp.aestronglyMeasurable v).sub (Lp.aestronglyMeasurable w)
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) one_le_two hm
  have h2 : eLpNorm (fun x => v x - w x) 2 μ = eLpNorm (⇑(v - w)) 2 μ :=
    eLpNorm_congr_ae (Lp.coeFn_sub v w).symm
  rw [h2] at h1
  have hne : eLpNorm (⇑(v - w)) 2 μ * μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
      ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top _)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top μ univ))
  calc ∫ x, |v x - w x| ∂μ = (eLpNorm (fun x => v x - w x) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm, ← integral_norm_eq_lintegral_enorm hm]
        · rfl
        · exact hm
    _ ≤ _ := ENNReal.toReal_mono hne h1
    _ = ‖v - w‖ * (μ univ).toReal ^ (1 / 2 : ℝ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, Lp.norm_def]
        norm_num

private lemma nonLinMinH1_lipschitz {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFb : ∃ M, ∀ t, |F t| ≤ M)
    (hF'b : ∃ M, ∀ t, |deriv F t| ≤ M) :
    Continuous fun v : Lp ℝ 2 μ => ∫ x, F (v x) ∂μ := by
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨L, hL⟩ := hF'b
  have hLip : LipschitzWith L.toNNReal F :=
    lipschitzWith_of_nnnorm_deriv_le (hF.differentiable one_ne_zero) fun t => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact (hL t).trans (le_max_left _ _)
  have hint : ∀ v : Lp ℝ 2 μ, Integrable (fun x => F (v x)) μ := fun v =>
    Integrable.of_bound (hF.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)) M
      (ae_of_all _ fun x => hM _)
  refine LipschitzWith.continuous (K := (max L 0 * (μ univ).toReal ^ (1 / 2 : ℝ)).toNNReal)
    (LipschitzWith.of_dist_le_mul fun v w => ?_)
  rw [Real.dist_eq, ← integral_sub (hint v) (hint w), dist_eq_norm,
    Real.coe_toNNReal _ (mul_nonneg (le_max_right _ _) (by positivity))]
  have hvw : Integrable (fun x => max L 0 * |v x - w x|) μ :=
    (((Lp.memLp v).sub (Lp.memLp w)).integrable one_le_two).norm.const_mul _
  calc |∫ x, F (v x) - F (w x) ∂μ| ≤ ∫ x, max L 0 * |v x - w x| ∂μ := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hvw (ae_of_all _ fun x => ?_)
        have := hLip.dist_le_mul (v x) (w x)
        rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal'] at this
        exact this
    _ = max L 0 * ∫ x, |v x - w x| ∂μ := integral_const_mul _ _
    _ ≤ max L 0 * (‖v - w‖ * (μ univ).toReal ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (nonLinMinH1_L1_le v w) (le_max_right _ _)
    _ = _ := by ring


private lemma nonLinMinH1_totBdd_subset {Ω : TopologicalSpace.Opens ℝᵈ}
    (h : TotallyBounded {f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω 2,
      ‖u‖ ≤ 1 ∧ (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val}) :
    TotallyBounded (nonLinMinH1_val Ω '' Metric.closedBall 0 1) := by
  refine h.subset ?_
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨u, by simpa using hu, ae_eq_refl _⟩

private lemma nonLinMinH1_totBdd_surCrit {Ω : TopologicalSpace.Opens ℝᵈ}
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω) (hd : d < 2) :
    TotallyBounded (nonLinMinH1_val Ω '' Metric.closedBall 0 1) := by
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have : CompactSpace (closure (Ω : Set ℝᵈ)) :=
    isCompact_iff_compactSpace.1 hΩb.isCompact_closure
  obtain ⟨hrep, hS⟩ := th_Rellich_surCritique Ω hΩb hΩ (p := 2) (by exact_mod_cast hd)
    (by norm_num)
  set K : ℝ := (measureUnivNNReal (volume.restrict (Ω : Set ℝᵈ)) : ℝ) ^
    (2 : ℝ≥0∞).toReal⁻¹
  have hK0 : 0 ≤ K := by positivity
  -- estimation `L²` par la norme uniforme des représentants continus
  have hest : ∀ (u v : H1 Ω) (g h : C(closure (Ω : Set ℝᵈ), ℝ)),
      (∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
        u.val x = g ⟨x, hx⟩) →
      (∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
        v.val x = h ⟨x, hx⟩) →
      dist (nonLinMinH1_val Ω u) (nonLinMinH1_val Ω v) ≤ K * dist g h := by
    intro u v g h hu hv
    rw [dist_eq_norm, nonLinMinH1_val_apply, nonLinMinH1_val_apply]
    refine Lp.norm_le_of_ae_bound dist_nonneg ?_
    filter_upwards [hu, hv, Lp.coeFn_sub u.val v.val, ae_restrict_mem hΩm] with x h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1 (subset_closure h4), h2 (subset_closure h4), ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, htS, htf, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded hS (ε / (K + 1)) (by positivity)
  have hU : ∀ g : t, ∃ u : H1 Ω, ‖u‖ ≤ 1 ∧
      ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
        u.val x = (g : C(closure (Ω : Set ℝᵈ), ℝ)) ⟨x, hx⟩ := fun g => htS g.2
  choose U hU1 hU2 using hU
  have : Finite t := htf.to_subtype
  refine ⟨range fun g : t => nonLinMinH1_val Ω (U g), finite_range _, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨g, hg⟩ := hrep u
  obtain ⟨y, hyt, hgy⟩ := mem_iUnion₂.1 (hcov ⟨u, by simpa using hu, hg⟩)
  refine mem_iUnion₂.2 ⟨_, mem_range_self ⟨y, hyt⟩, ?_⟩
  rw [Metric.mem_ball] at hgy ⊢
  calc dist (nonLinMinH1_val Ω u) (nonLinMinH1_val Ω (U ⟨y, hyt⟩)) ≤ K * dist g y :=
        hest _ _ _ _ hg (hU2 ⟨y, hyt⟩)
    _ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hgy.le hK0
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith


private lemma nonLinMinH1_compact {Ω : TopologicalSpace.Opens ℝᵈ}
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω) :
    IsCompactOperator (nonLinMinH1_val Ω) := by
  have hTB : TotallyBounded (nonLinMinH1_val Ω '' Metric.closedBall 0 1) := by
    rcases lt_trichotomy d 2 with hd | rfl | hd
    · exact nonLinMinH1_totBdd_surCrit hΩb hΩ hd
    · exact nonLinMinH1_totBdd_subset (th_Rellich_critique Ω hΩb hΩ (p := 2) (q := 2)
        (by norm_num) (by norm_num) (by norm_num)).2
    · have hd' : (2 : ℝ≥0∞) < d := by exact_mod_cast hd
      refine nonLinMinH1_totBdd_subset (th_Rellich_sousCritique Ω hΩb hΩ (p := 2) (q := 2)
        (pstar := (2⁻¹ - (d : ℝ≥0∞)⁻¹)⁻¹) (by norm_num) hd' (inv_inv _) ?_).2
      rw [ENNReal.lt_inv_iff_lt_inv]
      exact ENNReal.sub_lt_self (by norm_num) (by norm_num)
        (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top d))
  exact ⟨closure (nonLinMinH1_val Ω '' Metric.closedBall 0 1),
    hTB.closure.isCompact_of_isClosed isClosed_closure,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos)
      fun u hu => subset_closure (mem_image_of_mem _ hu)⟩

private lemma nonLinMinH1_weakCont {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) (hT : IsCompactOperator T)
    (A : Set E) (hA : Bornology.IsBounded A) :
    ContinuousOn (fun w : WeakSpace ℝ E => T ((toWeakSpace ℝ E).symm w))
      (toWeakSpace ℝ E '' A) := by
  obtain ⟨R, hR⟩ := hA.subset_closedBall 0
  set R' : ℝ := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h1 := prop_opCompactComplCont_boule (R' • T) (hT.smul R')
  have hmaps : MapsTo (fun w : WeakSpace ℝ E => R'⁻¹ • w) (toWeakSpace ℝ E '' A)
      (toWeakSpace ℝ E '' Metric.closedBall 0 1) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨R'⁻¹ • x, ?_, map_smul _ _ _⟩
    have hx' : ‖x‖ ≤ R' := (mem_closedBall_zero_iff.1 (hR hx)).trans (le_max_left _ _)
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR',
      inv_mul_le_iff₀ hR', mul_one]
    exact hx'
  refine (h1.comp (continuous_const_smul _).continuousOn hmaps).congr fun w _ => ?_
  simp [smul_smul, mul_inv_cancel₀ hR'.ne']


/-- Partie linéaire `ℓ(u) = ∫_Ω f u = ⟪f, u⟫_{L²}`. -/
private noncomputable def nonLinMinH1_lin (Ω : TopologicalSpace.Opens ℝᵈ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) : H1 Ω →L[ℝ] ℝ :=
  (innerSL ℝ f).comp (nonLinMinH1_val Ω)

private lemma nonLinMinH1_lin_apply {Ω : TopologicalSpace.Opens ℝᵈ}
    (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) (u : H1 Ω) :
    ∫ x in (Ω : Set ℝᵈ), f x * u.val x = nonLinMinH1_lin Ω f u := by
  rw [nonLinMinH1_integral_mul]
  rfl

/-- Extraction de `corol:Rellich` (`p = q = 2`) : `∇u_{φ n} ⇀ ∇uLim` faiblement dans
`L²(Ω)^d` et `u_{φ n} → uLim` dans `L²(Ω)`. -/
private lemma nonLinMinH1_extract (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    (u : ℕ → H1 Ω) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : H1 Ω) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ _ (u (φ n)).gradL) atTop
        (𝓝 (toWeakSpace ℝ _ uLim.gradL)) ∧
      Tendsto (fun n => (u (φ n)).val) atTop (𝓝 uLim.val) := by
  rcases lt_trichotomy d 2 with hd | rfl | hd
  · have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
    have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
      isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
    have : CompactSpace (closure (Ω : Set ℝᵈ)) :=
      isCompact_iff_compactSpace.1 hΩb.isCompact_closure
    obtain ⟨uLim, φ, hφ, hgr, g, gLim, hg, hgLim, hcv⟩ := corol_Rellich_surCritique Ω hΩb hΩ
      (p := 2) (by norm_num) (by exact_mod_cast hd) (by norm_num) u hu
    refine ⟨uLim, φ, hφ, hgr, ?_⟩
    set K : ℝ := (measureUnivNNReal (volume.restrict (Ω : Set ℝᵈ)) : ℝ) ^
      (2 : ℝ≥0∞).toReal⁻¹
    have hcv' := (tendsto_iff_dist_tendsto_zero.1 hcv).const_mul K
    rw [mul_zero] at hcv'
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hcv'
    rw [dist_eq_norm]
    refine Lp.norm_le_of_ae_bound dist_nonneg ?_
    filter_upwards [hg n, hgLim, Lp.coeFn_sub (u (φ n)).val uLim.val, ae_restrict_mem hΩm]
      with x h1 h2 h3 h4
    rw [h3, Pi.sub_apply, h1 (subset_closure h4), h2 (subset_closure h4), ← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist _
  · obtain ⟨uLim, φ, hφ, hg, hL⟩ := corol_Rellich_critique Ω hΩb hΩ (p := 2) (q := 2)
      (by norm_num) (by norm_num) (by norm_num) u hu
    exact ⟨uLim, φ, hφ, hg, (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 hL⟩
  · have hd' : (2 : ℝ≥0∞) < d := by exact_mod_cast hd
    obtain ⟨uLim, φ, hφ, hg, hL⟩ := corol_Rellich_sousCritique Ω hΩb hΩ (p := 2) (q := 2)
      (pstar := (2⁻¹ - (d : ℝ≥0∞)⁻¹)⁻¹) (by norm_num) hd' (inv_inv _) (by
        rw [ENNReal.lt_inv_iff_lt_inv]
        exact ENNReal.sub_lt_self (by norm_num) (by norm_num)
          (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top d))) u hu
    exact ⟨uLim, φ, hφ, hg, (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).2 hL⟩

/-- `J(u) = ½ ‖u‖²_{H¹} - ∫_Ω f u + ∫_Ω F(u)`. -/
private lemma nonLinMinH1_J_eq (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFb : ∃ M, ∀ t, |F t| ≤ M) (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) (u : H1 Ω) :
    fonctionnelleNonLin Ω f F u =
      (1 / 2) * ‖u‖ ^ 2 - nonLinMinH1_lin Ω f u + ∫ x in (Ω : Set ℝᵈ), F (u.val x) := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  obtain ⟨M, hM⟩ := hFb
  have hFint : Integrable (fun x => F (u.val x)) (volume.restrict (Ω : Set ℝᵈ)) :=
    Integrable.of_bound
      (hF.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u.val)) M
      (ae_of_all _ fun x => hM _)
  rw [← nonLinMinH1_lin_apply, nonLinMinH1_norm_sq_int]
  have hi : ∀ a b : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)),
      Integrable (fun x => a x * b x) (volume.restrict (Ω : Set ℝᵈ)) := fun a b =>
    (Lp.memLp a).integrable_mul (Lp.memLp b)
  have hsq : ∀ a : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)),
      Integrable (fun x => a x ^ 2) (volume.restrict (Ω : Set ℝᵈ)) := fun a => by
    simpa only [sq] using hi a a
  have h1 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2)
      (volume.restrict (Ω : Set ℝᵈ)) :=
    (integrable_finsetSum _ fun i _ => hsq (u.grad i)).const_mul _
  have h2 : Integrable (fun x => (1 / 2) * u.val x ^ 2) (volume.restrict (Ω : Set ℝᵈ)) :=
    (hsq _).const_mul _
  have h3 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2 + (1 / 2) * u.val x ^ 2)
      (volume.restrict (Ω : Set ℝᵈ)) := h1.add h2
  have h4 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2 + (1 / 2) * u.val x ^ 2 -
      f x * u.val x) (volume.restrict (Ω : Set ℝᵈ)) := h3.sub (hi f u.val)
  simp only [fonctionnelleNonLin]
  rw [integral_add h4 hFint, integral_sub h3 (hi f u.val), integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => hsq _]
  simp only [sq]
  ring

/-- `J(u) = ½ ‖∇u‖²_{L²} + (½ ‖u‖²_{L²} - ⟪f, u⟫_{L²} + ∫_Ω F(u))`. -/
private lemma nonLinMinH1_J_eq_grad (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hFb : ∃ M, ∀ t, |F t| ≤ M) (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) (u : H1 Ω) :
    fonctionnelleNonLin Ω f F u = (1 / 2) * ‖u.gradL‖ ^ 2 +
      ((1 / 2) * ‖u.val‖ ^ 2 - inner ℝ f u.val + ∫ x in (Ω : Set ℝᵈ), F (u.val x)) := by
  rw [nonLinMinH1_J_eq Ω hΩb hF hFb f u, nonLinMinH1_norm_sq, PiLp.norm_sq_eq_of_L2]
  simp only [Sobolev1.gradL_apply]
  rw [show nonLinMinH1_lin Ω f u = inner ℝ f u.val from rfl]
  ring

/-- **Ex. `ex:nonLinMinH1` (Minimisation d'une fonctionnelle non-linéaire sur `H¹`).** Soient
`Ω` borné ayant la propriété de prolongement de Sobolev, `F ∈ C¹_b(ℝ)` (`F` de classe `C¹`, `F`
et `F'` bornées) et `f ∈ L²(Ω)`. Alors `J` (`fonctionnelleNonLin`) admet un minimiseur sur
`H¹(Ω)`.
Preuve : celle du cours (suite minimisante bornée par coercivité, extraction par
`corol:Rellich` avec `p = q = 2`, passage à la limite) ; la semi-continuité faible de
`½ ‖∇u‖²` est obtenue par l'inégalité `⟪x, y⟫ - ½ ‖x‖² ≤ ½ ‖y‖²` plutôt que par une liminf.
Dépend des axiomes de Milman–Pettis et de Young faible (via `corol:Rellich`). -/
theorem ex_nonLinMinH1 (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFb : ∃ M, ∀ t, |F t| ≤ M)
    (hF'b : ∃ M, ∀ t, |deriv F t| ≤ M) (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∃ u : H1 Ω, ∀ v : H1 Ω, fonctionnelleNonLin Ω f F u ≤ fonctionnelleNonLin Ω f F v := by
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  set J := fonctionnelleNonLin Ω f F with hJ
  -- partie `L²` : `Φ(v) = ½ ‖v‖² - ⟪f, v⟫ + ∫ F(v)`, continue sur `L²(Ω)`
  set Φ : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)) → ℝ := fun v =>
    (1 / 2) * ‖v‖ ^ 2 - inner ℝ f v + ∫ x in (Ω : Set ℝᵈ), F (v x) with hΦ
  have hΦc : Continuous Φ :=
    (((continuous_norm.pow 2).const_mul _).sub (continuous_const.inner continuous_id)).add
      (nonLinMinH1_lipschitz hF hFb hF'b)
  have hJe : ∀ u, J u = (1 / 2) * ‖u.gradL‖ ^ 2 + Φ u.val :=
    nonLinMinH1_J_eq_grad Ω hΩb hF hFb f
  -- coercivité : `J(u) ≥ ½ ‖u‖² - ‖f‖ ‖u‖ - K`
  obtain ⟨M, hM⟩ := hFb
  obtain ⟨K, hK⟩ : ∃ K, ∀ u : H1 Ω, -K ≤ ∫ x in (Ω : Set ℝᵈ), F (u.val x) :=
    ⟨M * (volume.restrict (Ω : Set ℝᵈ)).real univ, fun u => by
      have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ω : Set ℝᵈ))
        (f := fun x => F (u.val x)) (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (hM _))
      rw [Real.norm_eq_abs] at h
      exact (abs_le.1 h).1⟩
  have hℓb : ∀ u, nonLinMinH1_lin Ω f u ≤ ‖f‖ * ‖u‖ := fun u => by
    rw [← nonLinMinH1_lin_apply, nonLinMinH1_integral_mul]
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (nonLinMinH1_norm_val_le u) (norm_nonneg _))
  have hcoer : ∀ u, (1 / 2) * ‖u‖ ^ 2 - ‖f‖ * ‖u‖ - K ≤ J u := fun u => by
    rw [hJ, nonLinMinH1_J_eq Ω hΩb hF ⟨M, hM⟩ f u]
    linarith [hℓb u, hK u]
  -- `J` est minorée ; suite minimisante
  have hbdd : BddBelow (range J) := ⟨-(‖f‖ ^ 2 / 2) - K, by
    rintro _ ⟨u, rfl⟩
    nlinarith [hcoer u, sq_nonneg (‖u‖ - ‖f‖)]⟩
  set m := sInf (range J)
  have hm : ∀ v, m ≤ J v := fun v => csInf_le hbdd ⟨v, rfl⟩
  have hseq : ∀ n : ℕ, ∃ u, J u < m + 1 / (n + 1) := fun n => by
    obtain ⟨_, ⟨u, rfl⟩, hu⟩ := exists_lt_of_csInf_lt (range_nonempty J)
      (lt_add_of_pos_right m (by positivity : (0 : ℝ) < 1 / (n + 1)))
    exact ⟨u, hu⟩
  choose u hu using hseq
  have hJu : Tendsto (fun n => J (u n)) atTop (𝓝 m) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add m
    rw [add_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => hm _)
      (fun n => (hu n).le)
  -- la suite minimisante est bornée dans `H¹(Ω)`
  have hub : ∃ C, ∀ n, ‖u n‖ ≤ C := ⟨2 * ‖f‖ + 2 * |m + 1 + K| + 1, fun n => by
    have h1 := hcoer (u n)
    have h2 : J (u n) ≤ m + 1 := by
      have : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith [hu n]
    by_contra hlt
    rw [not_le] at hlt
    nlinarith [abs_nonneg (m + 1 + K), le_abs_self (m + 1 + K), norm_nonneg (u n),
      norm_nonneg f]⟩
  -- extraction (`corol:Rellich`)
  obtain ⟨uLim, φ, hφ, hgrad, hval⟩ := nonLinMinH1_extract Ω hΩb hΩ u hub
  refine ⟨uLim, fun v => le_trans ?_ (hm v)⟩
  -- semi-continuité inférieure : `½ ‖x‖² = lim (⟪x, x_n⟫ - ½ ‖x‖²)` et
  -- `⟪x, x_n⟫ - ½ ‖x‖² ≤ ½ ‖x_n‖²`
  set x := uLim.gradL
  have hinner : Tendsto (fun n => inner ℝ x (u (φ n)).gradL) atTop (𝓝 (inner ℝ x x)) :=
    ((WeakBilin.eval_continuous (topDualPairing ℝ _).flip (innerSL ℝ x)).tendsto _).comp hgrad
  have ha : Tendsto (fun n => inner ℝ x (u (φ n)).gradL - (1 / 2) * ‖x‖ ^ 2 +
      Φ (u (φ n)).val) atTop (𝓝 (J uLim)) := by
    rw [hJe uLim]
    have h := (hinner.sub_const ((1 / 2) * ‖x‖ ^ 2)).add ((hΦc.tendsto _).comp hval)
    have h2 : inner ℝ x x - (1 / 2) * ‖x‖ ^ 2 + Φ uLim.val = (1 / 2) * ‖x‖ ^ 2 + Φ uLim.val := by
      rw [real_inner_self_eq_norm_sq]
      ring
    rw [h2] at h
    exact h
  refine le_of_tendsto_of_tendsto' ha (hJu.comp hφ.tendsto_atTop) fun n => ?_
  rw [Function.comp_apply, hJe (u (φ n))]
  nlinarith [real_inner_le_norm x (u (φ n)).gradL, sq_nonneg (‖x‖ - ‖(u (φ n)).gradL‖)]

/-- **Ex. `ex:nonLinMinH1`, hypothèses de `corol:minFctCvxRefl`.** Avec
`f₀(u) = ½ ‖u‖²_{H¹} - ∫_Ω f u` (convexe s.c.i.) et `g(u) = ∫_Ω F(u)` (faiblement continue sur
les bornés), les hypothèses du second point de `corol:minFctCvxRefl` sont vérifiées sur
`E = H¹(Ω)`, et `J = f₀ + g`.
Preuve : `H¹(Ω)` est hilbertien donc réflexif (Riesz) ; `g` est faiblement continue sur les
bornés car l'injection `H¹(Ω) → L²(Ω)` est un opérateur compact (`th:Rellich` avec
`p = q = 2`, via `C(Ω̄)` si `d ≤ 1`), et `v ↦ ∫_Ω F(v)` est lipschitzienne sur `L²(Ω)`. -/
theorem ex_nonLinMinH1_hypMinFctCvxRefl (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFb : ∃ M, ∀ t, |F t| ≤ M)
    (hF'b : ∃ M, ∀ t, |deriv F t| ≤ M) (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    let f₀ : H1 Ω → EReal := fun u =>
      (((1 / 2) * ‖u‖ ^ 2 - ∫ x in (Ω : Set ℝᵈ), f x * u.val x : ℝ) : EReal)
    let g : H1 Ω → ℝ := fun u => ∫ x in (Ω : Set ℝᵈ), F (u.val x)
    Reflexif (H1 Ω) ∧ (∀ u, f₀ u ≠ ⊥) ∧ Convex ℝ {q : H1 Ω × ℝ | f₀ q.1 ≤ q.2} ∧
      LowerSemicontinuous f₀ ∧
      (∀ A : Set (H1 Ω), Bornology.IsBounded A →
        ContinuousOn (fun w : WeakSpace ℝ (H1 Ω) => g ((toWeakSpace ℝ (H1 Ω)).symm w))
          (toWeakSpace ℝ (H1 Ω) '' A)) ∧
      (∃ M : ℝ, {u | f₀ u + g u ≤ M}.Nonempty ∧ Bornology.IsBounded {u | f₀ u + g u ≤ M}) ∧
      ∀ u, f₀ u + g u = (fonctionnelleNonLin Ω f F u : EReal) := by
  intro f₀ g
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have hf₀ : ∀ u, f₀ u = (((1 / 2) * ‖u‖ ^ 2 - nonLinMinH1_lin Ω f u : ℝ) : EReal) :=
    fun u => by simp only [f₀, nonLinMinH1_lin_apply]
  have hφc : Continuous fun u : H1 Ω => (1 / 2) * ‖u‖ ^ 2 - nonLinMinH1_lin Ω f u :=
    ((continuous_norm.pow 2).const_mul _).sub (nonLinMinH1_lin Ω f).continuous
  obtain ⟨M, hM⟩ := hFb
  have hFint : ∀ u : H1 Ω, Integrable (fun x => F (u.val x)) (volume.restrict (Ω : Set ℝᵈ)) :=
    fun u => Integrable.of_bound
      (hF.continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u.val)) M
      (ae_of_all _ fun x => hM _)
  refine ⟨nonLinMinH1_reflexif_sub (W1p Ω 2), fun u => by rw [hf₀]; exact EReal.coe_ne_bot _,
    ?_, ?_, ?_, ?_, ?_⟩
  · -- convexité de l'épigraphe
    have hcvx : ConvexOn ℝ univ fun u : H1 Ω => (1 / 2) * ‖u‖ ^ 2 - nonLinMinH1_lin Ω f u :=
      (((convexOn_univ_norm.pow fun _ _ => norm_nonneg _) 2).smul
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).sub
          ((nonLinMinH1_lin Ω f).toLinearMap.concaveOn convex_univ)
    have heq : {q : H1 Ω × ℝ | f₀ q.1 ≤ q.2} = {p | p.1 ∈ univ ∧
        (1 / 2) * ‖p.1‖ ^ 2 - nonLinMinH1_lin Ω f p.1 ≤ p.2} := by
      ext q
      simp only [mem_ofPred_eq, hf₀, EReal.coe_le_coe_iff, mem_univ, true_and]
    rw [heq]
    exact hcvx.convex_epigraph
  · -- semi-continuité inférieure
    rw [show f₀ = _ from funext hf₀]
    exact (continuous_coe_real_ereal.comp hφc).lowerSemicontinuous
  · -- continuité faible de `g` sur les bornés
    intro A hA
    exact (nonLinMinH1_lipschitz hF ⟨M, hM⟩ hF'b).comp_continuousOn
      (nonLinMinH1_weakCont _ (nonLinMinH1_compact hΩb hΩ) A hA)
  · -- coercivité
    obtain ⟨K, hK⟩ : ∃ K, ∀ u, -K ≤ g u := ⟨M * (volume.restrict (Ω : Set ℝᵈ)).real univ,
      fun u => by
        have h := norm_integral_le_of_norm_le_const (μ := volume.restrict (Ω : Set ℝᵈ))
          (f := fun x => F (u.val x)) (ae_of_all _ fun x => (Real.norm_eq_abs _).le.trans (hM _))
        rw [Real.norm_eq_abs] at h
        exact (abs_le.1 h).1⟩
    have hℓb : ∀ u, nonLinMinH1_lin Ω f u ≤ ‖f‖ * ‖u‖ := fun u => by
      rw [← nonLinMinH1_lin_apply, nonLinMinH1_integral_mul]
      exact (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (nonLinMinH1_norm_val_le u) (norm_nonneg _))
    refine ⟨g 0, ⟨0, ?_⟩, ?_⟩
    · change f₀ 0 + g 0 ≤ g 0
      rw [hf₀]
      simp
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨2 * ‖f‖ + 2 * |g 0 + K| + 1, fun u hu => ?_⟩
      have hu' : (1 / 2) * ‖u‖ ^ 2 - nonLinMinH1_lin Ω f u + g u ≤ g 0 := by
        have h : f₀ u + g u ≤ g 0 := hu
        rwa [hf₀, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
      have h1 := hℓb u
      have h2 := hK u
      rw [mem_closedBall_zero_iff]
      by_contra hlt
      rw [not_le] at hlt
      nlinarith [abs_nonneg (g 0 + K), le_abs_self (g 0 + K), norm_nonneg u, norm_nonneg f]
  · -- `f₀ + g = J`
    intro u
    rw [hf₀, ← EReal.coe_add, EReal.coe_eq_coe_iff, ← nonLinMinH1_lin_apply,
      nonLinMinH1_norm_sq_int]
    have hi : ∀ a b : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)),
        Integrable (fun x => a x * b x) (volume.restrict (Ω : Set ℝᵈ)) := fun a b =>
      (Lp.memLp a).integrable_mul (Lp.memLp b)
    have hsq : ∀ a : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)),
        Integrable (fun x => a x ^ 2) (volume.restrict (Ω : Set ℝᵈ)) := fun a => by
      simpa only [sq] using hi a a
    have h1 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2)
        (volume.restrict (Ω : Set ℝᵈ)) :=
      (integrable_finsetSum _ fun i _ => hsq (u.grad i)).const_mul _
    have h2 : Integrable (fun x => (1 / 2) * u.val x ^ 2) (volume.restrict (Ω : Set ℝᵈ)) :=
      (hsq _).const_mul _
    have h3 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2 + (1 / 2) * u.val x ^ 2)
        (volume.restrict (Ω : Set ℝᵈ)) := h1.add h2
    have h4 : Integrable (fun x => (1 / 2) * ∑ i, u.grad i x ^ 2 + (1 / 2) * u.val x ^ 2 -
        f x * u.val x) (volume.restrict (Ω : Set ℝᵈ)) := h3.sub (hi f u.val)
    simp only [g, fonctionnelleNonLin]
    rw [integral_add h4 (hFint u), integral_sub h3 (hi f u.val), integral_add h1 h2,
      integral_const_mul,
      integral_const_mul, integral_finsetSum _ fun i _ => hsq _]
    simp only [sq]
    ring

/-- **Ex. `ex:nonLinMinH1`, seconde preuve**, par le second point de `corol:minFctCvxRefl`
(`corol_minFctCvxRefl_perturbation`) et `ex_nonLinMinH1_hypMinFctCvxRefl`. Dépend de
l'axiome de Young faible, mais pas de Milman–Pettis. -/
theorem ex_nonLinMinH1' (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFb : ∃ M, ∀ t, |F t| ≤ M)
    (hF'b : ∃ M, ∀ t, |deriv F t| ≤ M) (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∃ u : H1 Ω, ∀ v : H1 Ω, fonctionnelleNonLin Ω f F u ≤ fonctionnelleNonLin Ω f F v := by
  obtain ⟨hR, hbot, hcvx, hlsc, hg, ⟨M, hne, hbd⟩, heq⟩ :=
    ex_nonLinMinH1_hypMinFctCvxRefl Ω hΩb hΩ hF hFb hF'b f
  obtain ⟨u, hu⟩ := corol_minFctCvxRefl_perturbation hR hbot hcvx hlsc _ hg M hne hbd
  refine ⟨u, fun v => ?_⟩
  have h := hu v
  rwa [heq u, heq v, EReal.coe_le_coe_iff] at h

end M1Analyse
