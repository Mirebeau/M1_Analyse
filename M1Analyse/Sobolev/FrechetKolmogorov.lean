/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import M1Analyse.Sobolev.ConvolutionLp
import M1Analyse.TopologieGenerale.Metrique

/-!
# §5.1 Théorème de Fréchet-Kolmogorov (`subsec:convLp`, suite)

Source : `Include/Sobolev.tex`, sous-section `subsec:convLp`, fin (après
`corol:testDenseLp`).

Conventions de `M1Analyse.Sobolev.ConvolutionLp` : `ℝ^d` est `EuclideanSpace ℝ (Fin d)` muni de
la mesure de Lebesgue, `Ω` est un ouvert (`TopologicalSpace.Opens ℝ^d`), et `L^p(Ω)` est l'espace
de Mathlib `Lp ℝ p (volume.restrict Ω)`. Une partie « précompacte » d'un espace métrique est une
partie `TotallyBounded` ; comme `L^p(Ω)` est complet, c'est équivalent à être relativement
compacte (`th_FrechetKolmogorov_isCompact_closure`).

`ex:operCompactL2` (`ex_operCompactL2`) est démontré par un argument de Hilbert–Schmidt
(approximation par des opérateurs de rang fini) plutôt que par Fréchet–Kolmogorov.

Non formalisé : `corol:convolTestFun` (convergence `ρ_ε ⋆ φ → (∫ ρ) φ` dans `𝓓(Ω)`) : la
topologie de `𝓓(Ω)` (`TestFunction`, limite inductive) rend l'énoncé et la preuve longs.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal Convolution BoundedContinuousFunction
open ContinuousLinearMap (lsmul)

namespace M1Analyse

section FrechetKolmogorov

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Borne uniforme d'une convolution : si `|ρ| ≤ M` et `g ∈ L^1`, alors
`|ρ ⋆ g| ≤ M ‖g‖_1`. -/
theorem norm_convolution_le_of_bound {ρ g : ℝᵈ → ℝ} {M : ℝ} (hM : ∀ x, ‖ρ x‖ ≤ M)
    (hg : Integrable g) (x : ℝᵈ) :
    ‖(ρ ⋆ g) x‖ ≤ M * ∫ t, ‖g t‖ := by
  rw [convolution_lsmul_swap, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.norm.const_mul M) (ae_of_all _ fun t => ?_)
  rw [smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

/-- Régularité lipschitzienne d'une convolution : si `ρ` est `L`-lipschitzienne et bornée et
`g ∈ L^1`, alors `ρ ⋆ g` est `L ‖g‖_1`-lipschitzienne. -/
theorem dist_convolution_le {ρ g : ℝᵈ → ℝ} {L : ℝ≥0} {M : ℝ} (hρ : LipschitzWith L ρ)
    (hM : ∀ x, ‖ρ x‖ ≤ M) (hg : Integrable g) (x y : ℝᵈ) :
    dist ((ρ ⋆ g) x) ((ρ ⋆ g) y) ≤ L * dist x y * ∫ t, ‖g t‖ := by
  have hi : ∀ z : ℝᵈ, Integrable (fun t => ρ (z - t) * g t) := fun z =>
    hg.bdd_mul (hρ.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun t => hM _)
  rw [dist_eq_norm, convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  rw [← integral_sub (hi x) (hi y), ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.norm.const_mul _) (ae_of_all _ fun t => ?_)
  rw [← sub_mul, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖ρ (x - t) - ρ (y - t)‖ = dist (ρ (x - t)) (ρ (y - t)) := (dist_eq_norm _ _).symm
    _ ≤ L * dist (x - t) (y - t) := hρ.dist_le_mul _ _
    _ = L * dist x y := by rw [dist_sub_right]

/-- Découpage d'une norme `L^p` selon une partie mesurable `K` : pour `p ≥ 1`,
`‖f‖_{L^p(S)} ≤ ‖f‖_{L^p(S ∩ K)} + ‖f‖_{L^p(S ∖ K)}`. -/
theorem eLpNorm_restrict_le_inter_add_diff {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {S K : Set X} (hK : MeasurableSet K) (f : X → ℝ) :
    eLpNorm f p (μ.restrict S) ≤
      eLpNorm f p (μ.restrict (S ∩ K)) + eLpNorm f p (μ.restrict (S \ K)) := by
  calc eLpNorm f p (μ.restrict S)
      = eLpNorm (K.indicator f + Kᶜ.indicator f) p (μ.restrict S) := by
        rw [indicator_self_add_compl K f]
    _ ≤ eLpNorm (K.indicator f) p (μ.restrict S) + eLpNorm (Kᶜ.indicator f) p (μ.restrict S) :=
        eLpNorm_add_le hp
    _ = _ := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hK,
          eLpNorm_indicator_eq_eLpNorm_restrict hK.compl, Measure.restrict_restrict hK,
          Measure.restrict_restrict hK.compl, inter_comm K, inter_comm Kᶜ, ← sdiff_eq]

/-- Existence d'un noyau régularisant lipschitzien : pour `η > 0`, il existe `ρ ≥ 0` continue,
lipschitzienne, bornée, à support compact dans `B(0, η)`, d'intégrale unité. -/
theorem exists_noyau_lipschitz {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝᵈ → ℝ, (∀ x, 0 ≤ ρ x) ∧ Integrable ρ ∧ ∫ x, ρ x = 1 ∧
      (∀ h, ρ h ≠ 0 → ‖h‖ < η) ∧ Continuous ρ ∧ HasCompactSupport ρ ∧
      (∃ L, LipschitzWith L ρ) ∧ ∃ M, ∀ x, ‖ρ x‖ ≤ M := by
  let φ : ContDiffBump (0 : ℝᵈ) := ⟨η / 2, η, half_pos hη, half_lt_self hη⟩
  have hρc : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hρcont : Continuous (φ.normed volume) := φ.continuous_normed
  refine ⟨φ.normed volume, φ.nonneg_normed, φ.integrable_normed, φ.integral_normed,
    fun h hh => ?_, hρcont, hρc, ContDiff.lipschitzWith_of_hasCompactSupport hρc
    (φ.contDiff_normed (n := 1)) one_ne_zero, hρcont.bounded_above_of_compact_support hρc⟩
  have : h ∈ Function.support (φ.normed volume) := hh
  rw [φ.support_normed_eq, mem_ball_zero_iff] at this
  exact this

/-- Estimation de régularisation locale (cf. `lem:convolTranslat`) : si `ρ ≥ 0` est d'intégrale
unité et supportée dans `B(0, η)`, si `K ⊆ ℝ^d` est mesurable et
`‖f - f(· - h)‖_{L^p(K)} ≤ E` pour `|h| < η`, alors
`‖f - ρ ⋆ (1_{K + B'(0, η)} f)‖_{L^p(K)} ≤ E`. -/
theorem eLpNorm_sub_convolution_indicator_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {ρ : ℝᵈ → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρ1 : ∫ x, ρ x = 1) {η : ℝ}
    (hρs : ∀ h, ρ h ≠ 0 → ‖h‖ < η) {K : Set ℝᵈ} (hK : MeasurableSet K) {f : ℝᵈ → ℝ}
    (hf : MemLp ((cthickening η K).indicator f) p) {E : ℝ≥0∞}
    (hE : ∀ h : ℝᵈ, ‖h‖ < η → eLpNorm (fun x => f x - f (x - h)) p (volume.restrict K) ≤ E) :
    eLpNorm (f - ρ ⋆ (cthickening η K).indicator f) p (volume.restrict K) ≤ E := by
  set g := (cthickening η K).indicator f with hg_def
  have hr0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hpt
  have hKK : K ⊆ cthickening η K := self_subset_cthickening K
  have H := lem_convolTranslat hp hpt hρ0 hρi hρ1 hf K
  have heq : eLpNorm (f - ρ ⋆ g) p (volume.restrict K) =
      eLpNorm (ρ ⋆ g - g) p (volume.restrict K) := by
    rw [eLpNorm_sub_comm]
    refine eLpNorm_congr_ae ((ae_restrict_mem hK).mono fun x hx => ?_)
    simp [hg_def, indicator_of_mem (hKK hx)]
  have H2 : ∫⁻ h, ENNReal.ofReal (ρ h) *
        eLpNorm (fun x => g (x - h) - g x) p (volume.restrict K) ^ p.toReal ≤
      ∫⁻ h, ENNReal.ofReal (ρ h) * E ^ p.toReal := by
    refine lintegral_mono fun h => ?_
    by_cases hh : ρ h = 0
    · simp [hh]
    have hhη := hρs h hh
    gcongr
    have he1 : eLpNorm (fun x => g (x - h) - g x) p (volume.restrict K) =
        eLpNorm (fun x => f x - f (x - h)) p (volume.restrict K) := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae ((ae_restrict_mem hK).mono fun x hx => ?_)
      have hx1 : x - h ∈ cthickening η K := mem_cthickening_of_dist_le (x - h) x η K hx (by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hhη.le)
      simp [hg_def, indicator_of_mem (hKK hx), indicator_of_mem hx1]
    rw [he1]
    exact hE h hhη
  have hρint : ∫⁻ h, ENNReal.ofReal (ρ h) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρ0), hρ1, ENNReal.ofReal_one]
  rw [lintegral_mul_const'' _ hρi.aestronglyMeasurable.aemeasurable.ennreal_ofReal, hρint,
    one_mul] at H2
  rw [heq]
  exact (ENNReal.rpow_le_rpow_iff hr0).1 (H.trans H2)

/-- Conséquence du théorème d'Ascoli (`th:AscoliLip`) : une famille `(u_i)_{i ∈ s}` de fonctions
réelles continues, uniformément bornées et uniformément lipschitziennes, est précompacte pour la
convergence uniforme sur tout compact `K`. -/
theorem exists_finite_approx_of_lipschitz {X ι : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (u : ι → X → ℝ) (hc : ∀ i, Continuous (u i)) (s : Set ι) {M L : ℝ}
    (hM : ∀ i ∈ s, ∀ x, ‖u i x‖ ≤ M)
    (hL : ∀ i ∈ s, ∀ x y, dist (u i x) (u i y) ≤ L * dist x y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t ⊆ s, t.Finite ∧ ∀ i ∈ s, ∃ j ∈ t, ∀ x ∈ K, dist (u i x) (u j x) < δ := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let T : ι → (↥K →ᵇ ℝ) := fun i =>
    BoundedContinuousFunction.mkOfCompact ⟨fun x => u i x, (hc i).comp continuous_subtype_val⟩
  have hT : ∀ i x, T i x = u i x := fun _ _ => rfl
  have hA : IsCompact (closure (T '' s)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℝ) M)
      (isCompact_closedBall _ _) _ ?_ ?_
    · rintro _ x ⟨i, hi, rfl⟩
      rw [mem_closedBall_zero_iff, hT]
      exact hM i hi x
    · refine Metric.equicontinuous_of_continuity_modulus (fun r => L * r) ?_ _ ?_
      · have : Tendsto (fun r : ℝ => L * r) (𝓝 0) (𝓝 (L * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        simpa using this
      · rintro x y ⟨_, i, hi, rfl⟩
        change dist (T i x) (T i y) ≤ _
        rw [hT, hT]
        exact hL i hi x y
  obtain ⟨t, htA, htf, hcov⟩ :=
    Metric.finite_approx_of_totallyBounded (hA.totallyBounded.subset subset_closure) δ hδ
  obtain ⟨t', ht's, ht'f, hcov'⟩ :=
    (Set.exists_subset_image_finite_and
      (p := fun t => T '' s ⊆ ⋃ y ∈ t, ball y δ)).1 ⟨t, htA, htf, hcov⟩
  refine ⟨t', ht's, ht'f, fun i hi => ?_⟩
  obtain ⟨_, ⟨j, hj, rfl⟩, hij⟩ : ∃ y ∈ T '' t', T i ∈ ball y δ := by
    simpa using hcov' (mem_image_of_mem T hi)
  refine ⟨j, hj, fun x hx => ?_⟩
  rw [← hT i ⟨x, hx⟩, ← hT j ⟨x, hx⟩]
  exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt (mem_ball.1 hij)

/-- **Th. `th:FrechetKolmogorov` (Fréchet-Kolmogorov).** Soit `p ∈ [1, ∞[`, `Ω ⊆ ℝ^d` ouvert et
`𝓕` une partie bornée de `L^p(Ω)` telle que
(i) (régularité sous translation) pour tout compact `K ⊆ Ω` il existe un module de continuité
`ω_K` tel que `‖f - f(· - h)‖_{L^p(K)} ≤ ω_K(|h|)` pour toute `f ∈ 𝓕` et tout `h` tel que
`|h| ≤ d(K, ℝ^d ∖ Ω)` ;
(ii) (masse évanescente au bord) pour tout `ε > 0` il existe un compact `K ⊆ Ω` tel que
`‖f‖_{L^p(Ω ∖ K)} ≤ ε` pour toute `f ∈ 𝓕`.
Alors `𝓕` est une partie précompacte de `L^p(Ω)`.
Remarque : la condition `|h| ≤ d(K, ℝ^d ∖ Ω)` est écrite `K + B'(0, |h|) ⊆ Ω`
(`cthickening ‖h‖ K ⊆ Ω`). Pour `K` compact et `Ω ≠ ℝ^d`, ceci équivaut à
`|h| < d(K, ℝ^d ∖ Ω)` : l'hypothèse (i) est donc (très légèrement) plus faible que celle du
cours, et le théorème plus fort ; elle garantit que `f(x - h)` n'est évaluée qu'en des points de
`Ω` (sans extension de `f` hors de `Ω`). Pour `Ω = ℝ^d` elle porte sur tout `h`, alors que la
convention de Mathlib `infDist x ∅ = 0` rendrait la formulation littérale dégénérée.
Les fonctions `f ∈ 𝓕` sont des classes de `L^p(Ω)` ; `f x` désigne un représentant. -/
theorem th_FrechetKolmogorov (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hpt : p ≠ ∞) (𝓕 : Set (Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))))
    (hb : Bornology.IsBounded 𝓕)
    (hi : ∀ K : Set ℝᵈ, IsCompact K → K ⊆ Ω → ∃ ω : ℝ≥0 → ℝ≥0∞, EstModuleCont ω ∧
      ∀ f ∈ 𝓕, ∀ h : ℝᵈ, cthickening ‖h‖ K ⊆ Ω →
        eLpNorm (fun x => f x - f (x - h)) p (volume.restrict K) ≤ ω ‖h‖₊)
    (hii : ∀ ε > (0 : ℝ), ∃ K : Set ℝᵈ, IsCompact K ∧ K ⊆ Ω ∧
      ∀ f ∈ 𝓕, eLpNorm f p (volume.restrict ((Ω : Set ℝᵈ) \ K)) ≤ ENNReal.ofReal ε) :
    TotallyBounded 𝓕 := by
  have hp1 : 1 ≤ p := Fact.out
  have hr0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp1).ne' hpt
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have hCe : ∀ f ∈ 𝓕, eLpNorm f p (volume.restrict (Ω : Set ℝᵈ)) ≤ ENNReal.ofReal C :=
    fun f hf => by
      rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f), ← Lp.norm_def]
      exact ENNReal.ofReal_le_ofReal (hC f hf)
  rw [EMetric.totallyBounded_iff]
  intro ε hε
  obtain ⟨a, -, ha, haε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have ha0 : 0 < a := ENNReal.ofReal_pos.1 ha
  obtain ⟨e, he0, hea⟩ : ∃ e : ℝ, 0 < e ∧ 5 * e = a := ⟨a / 5, by positivity, by ring⟩
  -- (ii) : le compact `K₀`
  obtain ⟨K₀, hK₀c, hK₀Ω, hK₀⟩ := hii e he0
  have hK₀m : MeasurableSet K₀ := hK₀c.measurableSet
  -- (i) : le module de continuité sur `K₀`
  obtain ⟨ω, hω, hωK⟩ := hi K₀ hK₀c hK₀Ω
  obtain ⟨η₁, hη₁, hη₁Ω⟩ := hK₀c.exists_cthickening_subset_open Ω.isOpen hK₀Ω
  obtain ⟨η₂, hη₂, hη₂ω⟩ :
      ∃ η₂ : ℝ, 0 < η₂ ∧ ∀ s : ℝ≥0, (s : ℝ) ≤ η₂ → ω s ≤ ENNReal.ofReal e := by
    have hev := hω.eventually (Iic_mem_nhds (ENNReal.ofReal_pos.2 he0))
    obtain ⟨δ, hδ, hδω⟩ := Metric.eventually_nhds_iff.1 hev
    refine ⟨δ / 2, half_pos hδ, fun s hs => hδω ?_⟩
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq]
    linarith
  obtain ⟨η, hη, hηη₁, hηη₂⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ η₁ ∧ η ≤ η₂ :=
    ⟨min η₁ η₂, lt_min hη₁ hη₂, min_le_left _ _, min_le_right _ _⟩
  have hK₁c : IsCompact (cthickening η K₀) := hK₀c.cthickening
  have hK₁m : MeasurableSet (cthickening η K₀) := hK₁c.measurableSet
  have hK₁Ω : cthickening η K₀ ⊆ Ω := (cthickening_mono hηη₁ K₀).trans hη₁Ω
  -- noyau régularisant `ρ`, supporté dans `B(0, η)`
  obtain ⟨ρ, hρ0, hρi, hρ1, hρs, hρcont, hρc, ⟨L, hL⟩, M, hM⟩ := exists_noyau_lipschitz hη
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  -- les fonctions tronquées `1_{K₁} f` et régularisées `ρ ⋆ (1_{K₁} f)`
  have hgp : ∀ f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)),
      MemLp f p (volume.restrict (cthickening η K₀)) := fun f =>
    (Lp.memLp f).mono_measure (Measure.restrict_mono hK₁Ω le_rfl)
  have hμK₁ : volume (cthickening η K₀) ≠ ∞ := hK₁c.measure_lt_top.ne
  have : IsFiniteMeasure (volume.restrict (cthickening η K₀)) :=
    isFiniteMeasure_restrict.2 hμK₁
  have hgi : ∀ f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)),
      Integrable ((cthickening η K₀).indicator f) := fun f => by
    rw [← memLp_one_iff_integrable]
    exact (memLp_indicator_iff_restrict hK₁m).2 ((hgp f).mono_exponent hp1)
  -- borne `L^1` uniforme
  obtain ⟨B, hB0, hgB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ f ∈ 𝓕,
      ∫ t, ‖(cthickening η K₀).indicator f t‖ ≤ B := by
    have hB'ne : ENNReal.ofReal C * volume (cthickening η K₀) ^
        (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by
        rw [ENNReal.toReal_one, div_one, sub_nonneg, div_le_one hr0, ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hpt hp1) hμK₁)
    refine ⟨(ENNReal.ofReal C * volume (cthickening η K₀) ^
      (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal)).toReal, ENNReal.toReal_nonneg, fun f hf => ?_⟩
    rw [integral_norm_eq_lintegral_enorm (hgi f).aestronglyMeasurable,
      ← eLpNorm_one_eq_lintegral_enorm]
    · refine ENNReal.toReal_mono hB'ne ?_
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hK₁m]
      refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp1 (hgp f).aestronglyMeasurable).trans ?_
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_left
        ((eLpNorm_mono_measure _ (Measure.restrict_mono hK₁Ω le_rfl)).trans (hCe f hf)) _
    · exact (hgi f).aestronglyMeasurable
  set u : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) → ℝᵈ → ℝ :=
    fun f => ρ ⋆ (cthickening η K₀).indicator f with hu_def
  have hu_cont : ∀ f, Continuous (u f) := fun f =>
    hρc.continuous_convolution_left (lsmul ℝ ℝ) hρcont (hgi f).locallyIntegrable
  -- estimation clé : `‖f - u f‖_{L^p(K₀)} ≤ e`
  have key : ∀ f ∈ 𝓕, eLpNorm (⇑f - u f) p (volume.restrict K₀) ≤ ENNReal.ofReal e :=
    fun f hf => eLpNorm_sub_convolution_indicator_le hp1 hpt hρ0 hρi hρ1 hρs hK₀m
      ((memLp_indicator_iff_restrict hK₁m).2 (hgp f)) fun h hh =>
        (hωK f hf h ((cthickening_mono (hh.le.trans hηη₁) K₀).trans hη₁Ω)).trans
          (hη₂ω _ (hh.le.trans hηη₂))
  -- rayon d'approximation uniforme
  have hμK₀ : volume K₀ ≠ ∞ := hK₀c.measure_lt_top.ne
  obtain ⟨c, hc0, hCc⟩ : ∃ c : ℝ, 0 ≤ c ∧ volume K₀ ^ p.toReal⁻¹ = ENNReal.ofReal c :=
    ⟨(volume K₀).toReal ^ p.toReal⁻¹, by positivity, by
      rw [← ENNReal.ofReal_toReal hμK₀, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg
        (by positivity), ENNReal.toReal_ofReal ENNReal.toReal_nonneg]⟩
  -- Ascoli
  obtain ⟨t, ht𝓕, htf, hcov⟩ := exists_finite_approx_of_lipschitz hK₀c u hu_cont 𝓕
    (M := M * B) (L := L * B)
    (fun f hf x => (norm_convolution_le_of_bound hM (hgi f) x).trans
      (mul_le_mul_of_nonneg_left (hgB f hf) hM0))
    (fun f hf x y => (dist_convolution_le hL hM (hgi f) x y).trans (by
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hgB f hf) L.2)
        dist_nonneg))
    (show 0 < e / (c + 1) by positivity)
  refine ⟨t, htf, fun f hf => ?_⟩
  obtain ⟨f', hf't, hff'⟩ := hcov f hf
  have hf' : f' ∈ 𝓕 := ht𝓕 hf't
  refine mem_iUnion₂.2 ⟨f', hf't, ?_⟩
  rw [mem_eball, Lp.edist_def]
  -- découpage `Ω = K₀ ∪ (Ω ∖ K₀)`
  have h1 := eLpNorm_restrict_le_inter_add_diff (μ := volume)
    (S := (Ω : Set ℝᵈ)) hp1 hK₀m (⇑f - ⇑f')
  rw [inter_eq_right.2 hK₀Ω] at h1
  have h2 : eLpNorm (⇑f - ⇑f') p (volume.restrict ((Ω : Set ℝᵈ) \ K₀)) ≤
      ENNReal.ofReal e + ENNReal.ofReal e :=
    (eLpNorm_sub_le hp1).trans (add_le_add (hK₀ f hf) (hK₀ f' hf'))
  have h3 : eLpNorm (u f - u f') p (volume.restrict K₀) ≤ ENNReal.ofReal e := by
    refine (eLpNorm_le_of_ae_bound (C := e / (c + 1))
      ((hu_cont f).sub (hu_cont f')).aestronglyMeasurable
      ((ae_restrict_mem hK₀m).mono fun x hx => ?_)).trans ?_
    · rw [Pi.sub_apply, ← dist_eq_norm]
      exact (hff' x hx).le
    · rw [Measure.restrict_apply_univ, hCc, ← ENNReal.ofReal_mul hc0]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      nlinarith
  have h4 : eLpNorm (⇑f - ⇑f') p (volume.restrict K₀) ≤
      ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal e := by
    have hdec : ⇑f - ⇑f' = (⇑f - u f) + (u f - u f') + (u f' - ⇑f') := by abel
    rw [hdec]
    refine (eLpNorm_add_le hp1).trans (add_le_add
      ((eLpNorm_add_le hp1).trans (add_le_add (key f hf) h3)) ?_)
    rw [eLpNorm_sub_comm]
    exact key f' hf'
  refine (h1.trans (add_le_add h4 h2)).trans_lt (lt_of_le_of_lt (le_of_eq ?_) haε)
  rw [show ∀ x : ℝ≥0∞, x + x + x + (x + x) = 5 * x from fun x => by ring,
    ← ENNReal.ofReal_ofNat 5, ← ENNReal.ofReal_mul (by norm_num), hea]

/-- **Th. `th:FrechetKolmogorov` (Fréchet-Kolmogorov), forme relativement compacte.** Sous les
hypothèses de `th_FrechetKolmogorov`, l'adhérence de `𝓕` est compacte dans `L^p(Ω)` (qui est
complet, de sorte que précompacité et relative compacité coïncident). -/
theorem th_FrechetKolmogorov_isCompact_closure (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hpt : p ≠ ∞) (𝓕 : Set (Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))))
    (hb : Bornology.IsBounded 𝓕)
    (hi : ∀ K : Set ℝᵈ, IsCompact K → K ⊆ Ω → ∃ ω : ℝ≥0 → ℝ≥0∞, EstModuleCont ω ∧
      ∀ f ∈ 𝓕, ∀ h : ℝᵈ, cthickening ‖h‖ K ⊆ Ω →
        eLpNorm (fun x => f x - f (x - h)) p (volume.restrict K) ≤ ω ‖h‖₊)
    (hii : ∀ ε > (0 : ℝ), ∃ K : Set ℝᵈ, IsCompact K ∧ K ⊆ Ω ∧
      ∀ f ∈ 𝓕, eLpNorm f p (volume.restrict ((Ω : Set ℝᵈ) \ K)) ≤ ENNReal.ofReal ε) :
    IsCompact (closure 𝓕) :=
  isCompact_iff_totallyBounded_isComplete.2
    ⟨(th_FrechetKolmogorov Ω hpt 𝓕 hb hi hii).closure, isClosed_closure.isComplete⟩

end FrechetKolmogorov

section OperCompactL2Aux

open scoped InnerProductSpace

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

private lemma operCompactL2_memLp (g f : Lp ℝ 2 μ) :
    MemLp (fun p : X × X => g p.1 * f p.2) 2 (μ.prod μ) := by
  have hg := Lp.memLp g
  have hf := Lp.memLp f
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · exact (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).mul
      (hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  · have := ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).1 hg).mul_prod
      ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf)
    simpa [mul_pow] using this

/-- Le produit tensoriel `g ⊗ f : (x, y) ↦ g x * f y`, vu dans `L²(μ ⊗ μ)`. -/
private noncomputable def operCompactL2_tens (g f : Lp ℝ 2 μ) : Lp ℝ 2 (μ.prod μ) :=
  (operCompactL2_memLp g f).toLp _

private lemma operCompactL2_tens_coeFn (g f : Lp ℝ 2 μ) :
    operCompactL2_tens g f =ᵐ[μ.prod μ] fun p => g p.1 * f p.2 :=
  MemLp.coeFn_toLp _

private lemma operCompactL2_ae_fst {g g' : X → ℝ} (h : g =ᵐ[μ] g') :
    (fun p : X × X => g p.1) =ᵐ[μ.prod μ] fun p => g' p.1 :=
  Measure.quasiMeasurePreserving_fst.ae_eq_comp h

private lemma operCompactL2_ae_snd {g g' : X → ℝ} (h : g =ᵐ[μ] g') :
    (fun p : X × X => g p.2) =ᵐ[μ.prod μ] fun p => g' p.2 :=
  Measure.quasiMeasurePreserving_snd.ae_eq_comp h

private lemma operCompactL2_inner_tens (g f a b : Lp ℝ 2 μ) :
    ⟪operCompactL2_tens g f, operCompactL2_tens a b⟫_ℝ = ⟪g, a⟫_ℝ * ⟪f, b⟫_ℝ := by
  simp only [L2.inner_def]
  rw [← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [operCompactL2_tens_coeFn g f, operCompactL2_tens_coeFn a b] with p h1 h2
  simp only [h1, h2, RCLike.inner_apply, conj_trivial]
  ring

private lemma operCompactL2_norm_tens (g f : Lp ℝ 2 μ) :
    ‖operCompactL2_tens g f‖ = ‖g‖ * ‖f‖ := by
  have h := operCompactL2_inner_tens g f g f
  simp only [real_inner_self_eq_norm_sq] at h
  rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), h, mul_pow]

private lemma operCompactL2_tens_add_left (g g' f : Lp ℝ 2 μ) :
    operCompactL2_tens (g + g') f = operCompactL2_tens g f + operCompactL2_tens g' f := by
  apply Lp.ext
  filter_upwards [operCompactL2_tens_coeFn (g + g') f, operCompactL2_tens_coeFn g f,
    operCompactL2_tens_coeFn g' f, Lp.coeFn_add (operCompactL2_tens g f)
    (operCompactL2_tens g' f), operCompactL2_ae_fst (Lp.coeFn_add g g')]
    with p h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5 ⊢
  rw [h1, h4, h2, h3, h5]
  ring

private lemma operCompactL2_tens_add_right (g f f' : Lp ℝ 2 μ) :
    operCompactL2_tens g (f + f') = operCompactL2_tens g f + operCompactL2_tens g f' := by
  apply Lp.ext
  filter_upwards [operCompactL2_tens_coeFn g (f + f'), operCompactL2_tens_coeFn g f,
    operCompactL2_tens_coeFn g f', Lp.coeFn_add (operCompactL2_tens g f)
    (operCompactL2_tens g f'), operCompactL2_ae_snd (Lp.coeFn_add f f')]
    with p h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5 ⊢
  rw [h1, h4, h2, h3, h5]
  ring

private lemma operCompactL2_tens_smul_left (c : ℝ) (g f : Lp ℝ 2 μ) :
    operCompactL2_tens (c • g) f = c • operCompactL2_tens g f := by
  apply Lp.ext
  filter_upwards [operCompactL2_tens_coeFn (c • g) f, operCompactL2_tens_coeFn g f,
    Lp.coeFn_smul c (operCompactL2_tens g f), operCompactL2_ae_fst (Lp.coeFn_smul c g)]
    with p h1 h2 h4 h5
  simp only [Pi.smul_apply, smul_eq_mul] at h4 h5 ⊢
  rw [h1, h4, h2, h5]
  ring

private lemma operCompactL2_tens_smul_right (c : ℝ) (g f : Lp ℝ 2 μ) :
    operCompactL2_tens g (c • f) = c • operCompactL2_tens g f := by
  apply Lp.ext
  filter_upwards [operCompactL2_tens_coeFn g (c • f), operCompactL2_tens_coeFn g f,
    Lp.coeFn_smul c (operCompactL2_tens g f), operCompactL2_ae_snd (Lp.coeFn_smul c f)]
    with p h1 h2 h4 h5
  simp only [Pi.smul_apply, smul_eq_mul] at h4 h5 ⊢
  rw [h1, h4, h2, h5]
  ring

/-- Pour `f` fixé, l'opérateur continu `g ↦ g ⊗ f`. -/
private noncomputable def operCompactL2_tensR (f : Lp ℝ 2 μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (μ.prod μ) :=
  LinearMap.mkContinuous
    { toFun := fun g => operCompactL2_tens g f
      map_add' := fun g g' => operCompactL2_tens_add_left g g' f
      map_smul' := fun c g => operCompactL2_tens_smul_left c g f } ‖f‖
    (fun g => by simp [operCompactL2_norm_tens, mul_comm])

private lemma operCompactL2_tensR_apply (f g : Lp ℝ 2 μ) :
    operCompactL2_tensR f g = operCompactL2_tens g f := rfl

private lemma operCompactL2_norm_tensR_le (f : Lp ℝ 2 μ) : ‖operCompactL2_tensR f‖ ≤ ‖f‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

private lemma operCompactL2_tensR_add (f f' : Lp ℝ 2 μ) :
    operCompactL2_tensR (f + f') = operCompactL2_tensR f + operCompactL2_tensR f' := by
  ext1 g
  simp [operCompactL2_tensR_apply, operCompactL2_tens_add_right]

private lemma operCompactL2_tensR_smul (c : ℝ) (f : Lp ℝ 2 μ) :
    operCompactL2_tensR (c • f) = c • operCompactL2_tensR f := by
  ext1 g
  simp [operCompactL2_tensR_apply, operCompactL2_tens_smul_right]

/-- L'opérateur à noyau `K ↦ 𝒦_K`, défini par dualité :
`⟪g, 𝒦_K f⟫ = ⟪g ⊗ f, K⟫`, i.e. `𝒦_K f = (g ↦ g ⊗ f)† K`. -/
private noncomputable def operCompactL2_op :
    Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun K f => ContinuousLinearMap.adjoint (operCompactL2_tensR f) K)
      (fun K K' f => map_add _ K K')
      (fun c K f => map_smul _ c K)
      (fun K f f' => by
        rw [operCompactL2_tensR_add, map_add]; rfl)
      (fun c K f => by
        rw [operCompactL2_tensR_smul, map_smulₛₗ, conj_trivial]; rfl))
    1 (fun K f => by
      simp only [LinearMap.mk₂_apply, one_mul]
      calc ‖ContinuousLinearMap.adjoint (operCompactL2_tensR f) K‖
          ≤ ‖ContinuousLinearMap.adjoint (operCompactL2_tensR f)‖ * ‖K‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖f‖ * ‖K‖ := by
            rw [LinearIsometryEquiv.norm_map]
            exact mul_le_mul_of_nonneg_right (operCompactL2_norm_tensR_le f) (norm_nonneg _)
        _ = ‖K‖ * ‖f‖ := mul_comm _ _)

private lemma operCompactL2_inner_op (K : Lp ℝ 2 (μ.prod μ)) (g f : Lp ℝ 2 μ) :
    ⟪g, operCompactL2_op K f⟫_ℝ = ⟪operCompactL2_tens g f, K⟫_ℝ := by
  change ⟪g, ContinuousLinearMap.adjoint (operCompactL2_tensR f) K⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_right, operCompactL2_tensR_apply]

/-- Noyau de rang un : `𝒦_{a ⊗ b} f = ⟪b, f⟫ a`. -/
private lemma operCompactL2_op_tens (a b : Lp ℝ 2 μ) :
    operCompactL2_op (operCompactL2_tens a b) =
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a).comp (innerSL ℝ b) := by
  ext1 f
  refine ext_inner_left ℝ fun g => ?_
  rw [operCompactL2_inner_op, operCompactL2_inner_tens]
  simp [real_inner_smul_right, mul_comm, real_inner_comm f b]

private lemma operCompactL2_isCompact_tens (a b : Lp ℝ 2 μ) :
    IsCompactOperator (operCompactL2_op (operCompactL2_tens a b)) := by
  rw [operCompactL2_op_tens]
  exact ((isCompactOperator_of_locallyCompactSpace_dom (innerSL ℝ b)).clm_comp
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) a) :)

private lemma operCompactL2_tens_indicator {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    operCompactL2_tens (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ))
        (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)) =
      indicatorConstLp 2 (hA.prod hB) (measure_ne_top (μ.prod μ) _) (1 : ℝ) := by
  apply Lp.ext
  filter_upwards [operCompactL2_tens_coeFn (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ))
      (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)),
    operCompactL2_ae_fst (indicatorConstLp_coeFn (hs := hA) (hμs := measure_ne_top μ A)
      (c := (1 : ℝ)) (p := 2)),
    operCompactL2_ae_snd (indicatorConstLp_coeFn (hs := hB) (hμs := measure_ne_top μ B)
      (c := (1 : ℝ)) (p := 2)),
    indicatorConstLp_coeFn (hs := hA.prod hB) (hμs := measure_ne_top (μ.prod μ) _)
      (c := (1 : ℝ)) (p := 2)] with p h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  by_cases hpA : p.1 ∈ A <;> by_cases hpB : p.2 ∈ B <;> simp [hpA, hpB]

/-- Les produits tensoriels `g ⊗ f` sont totaux dans `L²(μ ⊗ μ)` : un noyau orthogonal à
tous les `g ⊗ f` est nul (argument de classe monotone sur les rectangles mesurables). -/
private lemma operCompactL2_eq_zero (K : Lp ℝ 2 (μ.prod μ))
    (h : ∀ g f : Lp ℝ 2 μ, ⟪operCompactL2_tens g f, K⟫_ℝ = 0) : K = 0 := by
  have hK : Integrable K (μ.prod μ) := (Lp.memLp K).integrable one_le_two
  have hrect : ∀ A B, MeasurableSet A → MeasurableSet B →
      ∫ p in A ×ˢ B, K p ∂(μ.prod μ) = 0 := by
    intro A B hA hB
    have := h (indicatorConstLp 2 hA (measure_ne_top μ A) 1)
      (indicatorConstLp 2 hB (measure_ne_top μ B) 1)
    rwa [operCompactL2_tens_indicator, L2.inner_indicatorConstLp_one] at this
  have hall : ∀ S (_ : MeasurableSet S), ∫ p in S, K p ∂(μ.prod μ) = 0 := by
    refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
    · simp
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hrect A B hA hB
    · intro t ht h
      rw [setIntegral_compl ht hK, h, sub_zero, ← setIntegral_univ, ← univ_prod_univ]
      exact hrect _ _ MeasurableSet.univ MeasurableSet.univ
    · intro f hd hm hf
      rw [integral_iUnion hm hd hK.integrableOn]
      simp [hf]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  exact hK.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => hall s hs)

/-- Densité + fermeture : `𝒦_K` est compact pour tout `K ∈ L²(μ ⊗ μ)`. -/
private lemma operCompactL2_isCompactOperator (K : Lp ℝ 2 (μ.prod μ)) :
    IsCompactOperator (operCompactL2_op K) := by
  let S : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
    Submodule.span ℝ {u | ∃ g f : Lp ℝ 2 μ, operCompactL2_tens g f = u}
  let C : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
    (compactOperator (RingHom.id ℝ) (Lp ℝ 2 μ) (Lp ℝ 2 μ)).comap
      (operCompactL2_op (μ := μ)).toLinearMap
  have hSC : S ≤ C := by
    rw [Submodule.span_le]
    rintro _ ⟨g, f, rfl⟩
    exact operCompactL2_isCompact_tens g f
  have hC : IsClosed (C : Set (Lp ℝ 2 (μ.prod μ))) :=
    isClosed_setOfPred_isCompactOperator.preimage (operCompactL2_op (μ := μ)).continuous
  have hS : S.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    have : Sᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro K hK
      apply operCompactL2_eq_zero
      intro g f
      exact (Submodule.mem_orthogonal _ _).1 hK _ (Submodule.subset_span ⟨g, f, rfl⟩)
    rw [this, Submodule.bot_orthogonal_eq_top]
  have hKC : K ∈ C := Submodule.topologicalClosure_minimal S hSC hC (hS ▸ Submodule.mem_top)
  exact hKC

private lemma operCompactL2_integrable (K : Lp ℝ 2 (μ.prod μ)) (g f : Lp ℝ 2 μ) :
    Integrable (fun p : X × X => g p.1 * (K p * f p.2)) (μ.prod μ) := by
  refine (L2.integrable_inner (operCompactL2_tens g f) K).congr ?_
  filter_upwards [operCompactL2_tens_coeFn g f] with p hp
  simp only [hp, RCLike.inner_apply, conj_trivial]
  ring

private lemma operCompactL2_inner_eq (K : Lp ℝ 2 (μ.prod μ)) (g f : Lp ℝ 2 μ) :
    ⟪operCompactL2_tens g f, K⟫_ℝ = ∫ x, g x * ∫ y, K (x, y) * f y ∂μ ∂μ := by
  rw [L2.inner_def, integral_congr_ae (g := fun p : X × X => g p.1 * (K p * f p.2)) ?_]
  · rw [integral_prod _ (operCompactL2_integrable K g f)]
    simp_rw [integral_const_mul]
  · filter_upwards [operCompactL2_tens_coeFn g f] with p hp
    simp only [hp, RCLike.inner_apply, conj_trivial]
    ring

/-- Identification de `𝒦_K f` avec la formule intégrale `x ↦ ∫ K(x, y) f(y) dy`. -/
private lemma operCompactL2_ae (K : Lp ℝ 2 (μ.prod μ)) (f : Lp ℝ 2 μ) :
    operCompactL2_op K f =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂μ := by
  have hone : Integrable (fun p : X × X => K p * f p.2) (μ.prod μ) := by
    refine (operCompactL2_integrable K
      (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ _) (1 : ℝ)) f).congr ?_
    filter_upwards [operCompactL2_ae_fst (indicatorConstLp_coeFn (hs := MeasurableSet.univ)
      (hμs := measure_ne_top μ _) (c := (1 : ℝ)) (p := 2))] with p hp
    rw [hp]
    simp
  have hF := hone.integral_prod_left
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ _ => ((Lp.memLp (operCompactL2_op K f)).integrable one_le_two).integrableOn)
    (fun s _ _ => hF.integrableOn) ?_
  intro s hs _
  rw [← L2.inner_indicatorConstLp_one hs (measure_ne_top μ s), operCompactL2_inner_op,
    operCompactL2_inner_eq, ← integral_indicator hs]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (hs := hs) (hμs := measure_ne_top μ s)
    (c := (1 : ℝ)) (p := 2)] with x hx
  rw [hx]
  by_cases hxs : x ∈ s <;> simp [hxs]

end OperCompactL2Aux

/-- **Ex. `ex:operCompactL2` (Compacité d'un opérateur intégral, version L²).**
Pour tout `K ∈ L²([0,1]², ℝ)`, l'endomorphisme de `L²([0,1])` défini par
`𝒦(f)(x) := ∫₀¹ K(x, y) f(y) dy` est compact.

Ici `[0,1]` est `Icc 0 1` muni de la mesure de Lebesgue restreinte, et `L²([0,1]²)` est
relatif à la mesure produit de cette mesure par elle-même. L'énoncé fournit un opérateur
continu `T` compact, qui coïncide presque partout avec la formule intégrale.

Route suivie (différente du cours, qui utilise Fréchet–Kolmogorov) : `𝒦_K` est défini par
dualité, `⟪g, 𝒦_K f⟫ = ⟪g ⊗ f, K⟫`, ce qui donne `‖𝒦_K‖ ≤ ‖K‖₂` et la continuité de
`K ↦ 𝒦_K` ; pour `K = a ⊗ b` l'opérateur est de rang un, donc compact ; les `a ⊗ b` sont
totaux dans `L²([0,1]²)` (classe monotone sur les rectangles) et les opérateurs compacts
forment un fermé, d'où la compacité pour tout `K` (argument de Hilbert–Schmidt). -/
theorem ex_operCompactL2 (K : Lp ℝ 2 ((volume.restrict (Icc (0 : ℝ) 1)).prod
      (volume.restrict (Icc (0 : ℝ) 1)))) :
    ∃ T : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)) →L[ℝ] Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
      IsCompactOperator T ∧ ∀ f : Lp ℝ 2 (volume.restrict (Icc (0 : ℝ) 1)),
        T f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
          fun x => ∫ y in Icc (0 : ℝ) 1, K (x, y) * f y :=
  ⟨operCompactL2_op K, operCompactL2_isCompactOperator K, operCompactL2_ae K⟩

end M1Analyse
