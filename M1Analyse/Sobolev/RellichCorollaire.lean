/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.Rellich
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# §5.5 Théorème de Rellich, version séquentielle (`corol:Rellich`)

Source : `Include/Sobolev.tex`, `corol:Rellich`, en trois théorèmes suivant les cas de
`th:Rellich` (mêmes hypothèses : `Ω` borné, `ProlongementSobolevTout Ω`, `1 < p < ∞`).

Preuve (différente du cours) : la réflexivité de `W^{1,p}(Ω)` (inégalités de Clarkson) est
remplacée par celle de `L^p(Ω)` (`reflexif_Lp`), appliquée composante par composante à
`(u, ∂₁u, …, ∂_d u)` ; la limite faible est dans `W^{1,p}(Ω)`, convexe fermé donc faiblement
fermé. Dépend de l'axiome de Milman–Pettis (via `reflexif_Lp`, `th_lpDualLq_bijectif`), et de
celui de Young faible dans les cas sous-critique et critique (via `th:Rellich`).
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ### Outils : compacité faible séquentielle -/

/-- Convergence faible d'une suite : convergence de `f (x n)` pour toute `f ∈ E^*`. -/
private lemma corolRellich_tendsto_weak {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℕ → E} {x₀ : E} :
    Tendsto (fun n => toWeakSpace ℝ E (x n)) atTop (𝓝 (toWeakSpace ℝ E x₀)) ↔
      ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x n)) atTop (𝓝 (f x₀)) := by
  refine WeakBilin.tendsto_iff_forall_eval_tendsto _ (fun a b h => ?_)
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)]
  exact fun φ => LinearMap.congr_fun h φ

/-- Dans un evn réflexif de dual séparable, toute suite bornée a une sous-suite faiblement
convergente (Banach–Alaoglu séquentiel dans le bidual). -/
private lemma corolRellich_weakSeq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Reflexif E) [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] (x : ℕ → E) (C : ℝ)
    (hx : ∀ n, ‖x n‖ ≤ C) :
    ∃ (x₀ : E) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f x₀)) := by
  set y : ℕ → WeakDual ℝ (StrongDual ℝ E) :=
    fun n => StrongDual.toWeakDual (NormedSpace.inclusionInDoubleDual ℝ E (x n)) with hy
  have hyK : ∀ n, y n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ _) C :=
    fun n => by
      exact (dist_zero_right (NormedSpace.inclusionInDoubleDual ℝ E (x n))).trans_le
        ((NormedSpace.double_dual_bound ℝ E (x n)).trans (hx n))
  obtain ⟨a, -, φ, hφ, ha⟩ := WeakDual.isSeqCompact_closedBall ℝ (StrongDual ℝ E) 0 C hyK
  obtain ⟨x₀, hx₀⟩ := hE.2 (WeakDual.toStrongDual a)
  refine ⟨x₀, φ, hφ, fun f => ?_⟩
  have := ((WeakBilin.eval_continuous _ f).tendsto a).comp ha
  have h2 : (topDualPairing ℝ (StrongDual ℝ E)) a f = f x₀ := (DFunLike.congr_fun hx₀ f).symm
  rw [h2] at this
  exact this

/-- Extraction simultanée sur un nombre fini de coordonnées. -/
private lemma corolRellich_weakSeq_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hE : Reflexif E) [TopologicalSpace.SeparableSpace (StrongDual ℝ E)] {ι : Type*}
    [Finite ι] (C : ℝ) :
    ∀ x : ℕ → ι → E, (∀ n i, ‖x n i‖ ≤ C) → ∃ (x₀ : ι → E) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i, ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x (φ n) i)) atTop (𝓝 (f (x₀ i))) := by
  classical
  have := Fintype.ofFinite ι
  suffices h : ∀ s : Finset ι, ∀ x : ℕ → ι → E, (∀ n i, ‖x n i‖ ≤ C) →
      ∃ (x₀ : ι → E) (φ : ℕ → ℕ), StrictMono φ ∧
        ∀ i ∈ s, ∀ f : StrongDual ℝ E, Tendsto (fun n => f (x (φ n) i)) atTop (𝓝 (f (x₀ i))) by
    intro x hx
    obtain ⟨x₀, φ, hφ, h⟩ := h Finset.univ x hx
    exact ⟨x₀, φ, hφ, fun i => h i (Finset.mem_univ i)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact fun x _ => ⟨x 0, id, strictMono_id, fun i hi => absurd hi (by simp)⟩
  | insert j s _ ih =>
    intro x hx
    obtain ⟨x₀, φ, hφ, h⟩ := ih x hx
    obtain ⟨y, ψ, hψ, hy⟩ := corolRellich_weakSeq hE (fun n => x (φ n) j) C (fun n => hx _ _)
    refine ⟨Function.update x₀ j y, φ ∘ ψ, hφ.comp hψ, fun i hi f => ?_⟩
    rcases eq_or_ne i j with rfl | hij
    · rw [Function.update_self]
      exact hy f
    · rw [Function.update_of_ne hij]
      exact (h i ((Finset.mem_insert.1 hi).resolve_left hij) f).comp hψ.tendsto_atTop

/-- `(L^p)^*` est séparable pour `1 < p < ∞` (image de `L^{p'}` séparable). -/
private lemma corolRellich_sepDual {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [MeasurableSpace.CountablyGenerated X] [SFinite μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p) (hp' : p ≠ ∞) :
    TopologicalSpace.SeparableSpace (StrongDual ℝ (Lp ℝ p μ)) := by
  set q := ENNReal.conjExponent p with hq
  have : q.HolderConjugate p := (inferInstance : p.HolderConjugate q).symm
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have : Fact (q ≠ ∞) := ⟨by
    rw [hq, ENNReal.conjExponent]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 (tsub_pos_of_lt hp).ne'⟩⟩
  exact (th_lpDualLq_bijectif (μ := μ) (q := q) hp hp').2.denseRange.separableSpace
    (dualLp μ p q).continuous

/-! ### Extraction faible dans `W^{1,p}(Ω)` -/

/-- Injection de la composante `u` dans `L^p(Ω) × L^p(Ω)^d`. -/
private noncomputable def corolRellich_inj0 (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) →L[ℝ] LpGrad Ω p :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℝ _ _

/-- Injection de la composante `∂ᵢ u` dans `L^p(Ω) × L^p(Ω)^d`. -/
private noncomputable def corolRellich_inj (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (i : Fin d) : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) →L[ℝ] LpGrad Ω p :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℝ _ _ ∘L
      (PiLp.continuousLinearEquiv p ℝ _).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single ℝ (fun _ : Fin d => Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) i

private lemma corolRellich_decomp (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (U : LpGrad Ω p) :
    U = corolRellich_inj0 Ω p U.fst + ∑ i, corolRellich_inj Ω p i (U.snd i) := by
  refine WithLp.ofLp_injective p (Prod.ext ?_ ?_)
  · simp [corolRellich_inj0, corolRellich_inj, Prod.fst_sum]
  · refine PiLp.ext fun j => ?_
    simp [corolRellich_inj0, corolRellich_inj, Prod.snd_sum, WithLp.ofLp_sum, Finset.sum_apply,
      PiLp.ofLp_single, Pi.single_apply]

/-- Toute suite bornée de `W^{1,p}(Ω)` (`1 < p < ∞`) a une sous-suite faiblement convergente
dans `L^p(Ω) × L^p(Ω)^d`, de limite dans `W^{1,p}(Ω)` (fermé convexe, donc faiblement fermé). -/
private lemma corolRellich_weakSobolev (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 1 < p) (hp' : p ≠ ∞) (u : ℕ → Sobolev1 Ω p) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧ ∀ T : StrongDual ℝ (LpGrad Ω p),
      Tendsto (fun n => T (u (φ n) : LpGrad Ω p)) atTop (𝓝 (T (uLim : LpGrad Ω p))) := by
  have hR := reflexif_Lp (μ := volume.restrict (Ω : Set ℝᵈ)) hp hp'
  have := corolRellich_sepDual (volume.restrict (Ω : Set ℝᵈ)) hp hp'
  obtain ⟨v, φ₁, hφ₁, hv⟩ := corolRellich_weakSeq hR (fun n => (u n).val) C
    (fun n => (WithLp.norm_fst_le (x := (u n : LpGrad Ω p))).trans (hu n))
  obtain ⟨g, φ₂, hφ₂, hg⟩ := corolRellich_weakSeq_pi hR C (fun n i => (u (φ₁ n)).grad i)
    (fun n i => ((PiLp.norm_apply_le _ i).trans
      (WithLp.norm_snd_le (x := (u (φ₁ n) : LpGrad Ω p)))).trans (hu _))
  set w : LpGrad Ω p := WithLp.toLp p (v, WithLp.toLp p g) with hw_def
  have hT : ∀ T : StrongDual ℝ (LpGrad Ω p),
      Tendsto (fun n => T (u (φ₁ (φ₂ n)) : LpGrad Ω p)) atTop (𝓝 (T w)) := by
    intro T
    have e : ∀ U : LpGrad Ω p, T U = (T ∘L corolRellich_inj0 Ω p) U.fst +
        ∑ i, (T ∘L corolRellich_inj Ω p i) (U.snd i) := by
      intro U
      conv_lhs => rw [corolRellich_decomp Ω p U]
      simp only [map_add, map_sum, ContinuousLinearMap.comp_apply]
    simp_rw [e]
    exact ((hv _).comp hφ₂.tendsto_atTop).add (tendsto_finsetSum _ fun i _ => hg i _)
  have hwT := corolRellich_tendsto_weak.2 hT
  have hcl : IsClosed (toWeakSpace ℝ _ '' (W1p Ω p : Set (LpGrad Ω p))) := by
    have := (W1p Ω p).convex.toWeakSpace_closure (𝕜 := ℝ)
    rw [(prop_SobolevBanach_isClosed Ω p).closure_eq] at this
    rw [this]
    exact isClosed_closure
  have hw : w ∈ W1p Ω p := by
    obtain ⟨w', hw', hww'⟩ := hcl.mem_of_tendsto hwT
      (Eventually.of_forall fun n => mem_image_of_mem _ (u (φ₁ (φ₂ n))).2)
    rwa [(toWeakSpace ℝ _).injective hww'] at hw'
  exact ⟨⟨w, hw⟩, φ₁ ∘ φ₂, hφ₁.comp hφ₂, hT⟩

/-- Une limite faible dans `L^p` et une limite forte dans `L^r` (mesure finie) coïncident p.p. :
on teste contre les indicatrices `1_s`, `s` mesurable. -/
private lemma corolRellich_ae_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {p r : ℝ≥0∞} [Fact (1 ≤ p)] (hr : 1 ≤ r) (f : ℕ → Lp ℝ p μ)
    (v : Lp ℝ p μ) (hw : ∀ T : StrongDual ℝ (Lp ℝ p μ), Tendsto (fun n => T (f n)) atTop (𝓝 (T v)))
    {h : X → ℝ} (hh : MemLp h r μ)
    (hs : Tendsto (fun n => eLpNorm (fun x => f n x - h x) r μ) atTop (𝓝 0)) :
    (v : X → ℝ) =ᵐ[μ] h := by
  set q := ENNReal.conjExponent p with hq
  have : q.HolderConjugate p := (inferInstance : p.HolderConjugate q).symm
  have : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hint : ∀ g : Lp ℝ p μ, Integrable g μ := fun g => (Lp.memLp g).integrable Fact.out
  have hhi : Integrable h μ := hh.integrable hr
  have hL1 : Tendsto (fun n => ∫⁻ x, ‖f n x - h x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hr1 : 1 / r.toReal ≤ 1 := by
      rcases eq_or_ne r ∞ with rfl | hrt
      · simp
      · exact div_le_one_of_le₀ (by simpa using ENNReal.toReal_mono hrt hr) ENNReal.toReal_nonneg
    have hc : μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / r.toReal) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by
        rw [ENNReal.toReal_one, div_one, sub_nonneg]
        exact hr1) (measure_ne_top μ univ)
    have := ENNReal.Tendsto.mul_const hs (Or.inr hc)
    rw [zero_mul] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le)
      fun n => ?_
    have hm : AEStronglyMeasurable (fun x => f n x - h x) μ :=
      (Lp.aestronglyMeasurable (f n)).sub hh.aestronglyMeasurable
    refine le_of_eq_of_le ?_ (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hr hm)
    rw [eLpNorm_one_eq_lintegral_enorm hm]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ _ => (hint v).integrableOn)
    (fun s _ _ => hhi.integrableOn) fun s hs hμs => ?_
  set T := dualLp μ p q (indicatorConstLp q hs hμs.ne (1 : ℝ))
  have hT : ∀ g : Lp ℝ p μ, T g = ∫ x in s, g x ∂μ := by
    intro g
    rw [dualLp_apply, ← integral_indicator hs]
    refine integral_congr_ae ?_
    filter_upwards [indicatorConstLp_coeFn (p := q) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))]
      with x hx
    rw [hx]
    by_cases hxs : x ∈ s <;> simp [hxs]
  have h1 := hw T
  simp_rw [hT] at h1
  exact tendsto_nhds_unique h1
    (tendsto_setIntegral_of_L1 h hh.aestronglyMeasurable
      (Eventually.of_forall fun n => hint (f n)) hL1 s)

/-- Extraction d'une sous-suite convergente dans une partie précompacte d'un espace complet. -/
private lemma corolRellich_seq_totallyBounded {Y : Type*} [UniformSpace Y] [CompleteSpace Y]
    [FirstCountableTopology Y] {S : Set Y} (hS : TotallyBounded S) (z : ℕ → Y)
    (hz : ∀ n, z n ∈ S) :
    ∃ (z₀ : Y) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (fun n => z (φ n)) atTop (𝓝 z₀) := by
  obtain ⟨z₀, -, φ, hφ, h⟩ := (hS.closure.isCompact_of_isClosed isClosed_closure).isSeqCompact
    (fun n => subset_closure (hz n))
  exact ⟨z₀, φ, hφ, h⟩

private lemma corolRellich_val_smul (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : ℝ) (u : Sobolev1 Ω p) : (c • u).val = c • u.val :=
  rfl

/-- Cas `L^q` (sous-critique et critique) : conclusion de `corol:Rellich` à partir de celle de
`th:Rellich`. -/
private lemma corolRellich_Lq (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ))
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hpt : p ≠ ∞)
    (hM : ∀ u : Sobolev1 Ω p, MemLp (u.val : ℝᵈ → ℝ) q (volume.restrict (Ω : Set ℝᵈ)))
    (hTB : TotallyBounded {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω p,
      ‖u‖ ≤ 1 ∧ (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val})
    (u : ℕ → Sobolev1 Ω p) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ T : StrongDual ℝ (LpGrad Ω p),
        Tendsto (fun n => T (u (φ n) : LpGrad Ω p)) atTop (𝓝 (T (uLim : LpGrad Ω p)))) ∧
      Tendsto (fun n => eLpNorm (fun x => (u (φ n)).val x - uLim.val x) q
        (volume.restrict (Ω : Set ℝᵈ))) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hu
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  obtain ⟨uLim, φ₁, hφ₁, hT⟩ := corolRellich_weakSobolev Ω hp hpt u C hC
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = max C 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := hc_def ▸ lt_of_lt_of_le one_pos (le_max_right C 1)
  have hcu : ∀ n, ‖c⁻¹ • u n‖ ≤ 1 := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, inv_mul_le_iff₀ hc0, mul_one,
      hc_def]
    exact (hC _).trans (le_max_left C 1)
  obtain ⟨z, hz_def⟩ : ∃ z : ℕ → Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)),
      z = fun n => (hM (c⁻¹ • u (φ₁ n))).toLp _ := ⟨_, rfl⟩
  have hzae : ∀ n, (z n : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] (c⁻¹ • u (φ₁ n)).val :=
    fun n => hz_def ▸ MemLp.coeFn_toLp _
  have hz : ∀ n, z n ∈ {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω p,
      ‖u‖ ≤ 1 ∧ (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val} :=
    fun n => ⟨c⁻¹ • u (φ₁ n), hcu _, hzae n⟩
  obtain ⟨z₀, φ₂, hφ₂, hz₀⟩ := corolRellich_seq_totallyBounded hTB z hz
  refine ⟨uLim, φ₁ ∘ φ₂, hφ₁.comp hφ₂, ?_, ?_⟩
  · exact fun T => (hT T).comp hφ₂.tendsto_atTop
  have hval : ∀ n, ((u (φ₁ (φ₂ n))).val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)]
      (c • z (φ₂ n) : Lp ℝ q _) := by
    intro n
    filter_upwards [Lp.coeFn_smul c (z (φ₂ n)), hzae (φ₂ n),
      Lp.coeFn_smul c⁻¹ (u (φ₁ (φ₂ n))).val] with x h1 h2 h3
    rw [h1, Pi.smul_apply, h2, corolRellich_val_smul, h3, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, mul_inv_cancel_left₀ hc0.ne']
  have hconv : Tendsto (fun n => eLpNorm (fun x => (u (φ₁ (φ₂ n))).val x - (c • z₀ : Lp ℝ q _) x)
      q (volume.restrict (Ω : Set ℝᵈ))) atTop (𝓝 0) := by
    refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 (hz₀.const_smul c)).congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hval n] with x hx
    rw [Pi.sub_apply, hx]
  have hid := corolRellich_ae_eq (Fact.out : 1 ≤ q) (fun n => (u (φ₁ (φ₂ n))).val) uLim.val
    (fun T => (hT (T ∘L WithLp.fstL p ℝ _ _)).comp hφ₂.tendsto_atTop) (Lp.memLp _) hconv
  refine hconv.congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [hid] with x hx
  rw [hx]
  rfl

/-- **Cor. `corol:Rellich` (Rellich, séquentiel), cas sous-critique.** Soient `Ω` borné ayant
la propriété de prolongement de Sobolev, `1 < p < d`, `1/p* = 1/p - 1/d` et `q ∈ [1, p*[`. Pour
toute suite `(u_n)` bornée dans `W^{1,p}(Ω)`, il existe `u_* ∈ W^{1,p}(Ω)` (`uLim`) et une
extractrice `φ` tels que `∇u_{φ(n)} ⇀ ∇u_*` faiblement dans `L^p(Ω)^d` et `u_{φ(n)} → u_*`
dans `L^q(Ω)`.
Preuve (différente du cours) : extractions faibles composante par composante dans `L^p(Ω)`
(réflexif, de dual séparable) au lieu de la réflexivité de `W^{1,p}(Ω)` ; la limite est dans
`W^{1,p}(Ω)`, faiblement fermé ; une nouvelle extraction converge fortement par `th:Rellich`
(précompacité), et les deux limites coïncident p.p. (test contre les indicatrices).
Dépend des axiomes de Milman–Pettis et de Young faible. -/
theorem corol_Rellich_sousCritique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p pstar q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hpd : p < d)
    (hpstar : pstar⁻¹ = p⁻¹ - (d : ℝ≥0∞)⁻¹) (hq : q < pstar)
    (u : ℕ → Sobolev1 Ω p) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ _ (u (φ n)).gradL) atTop
        (𝓝 (toWeakSpace ℝ _ uLim.gradL)) ∧
      Tendsto (fun n => eLpNorm (fun x => (u (φ n)).val x - uLim.val x) q
        (volume.restrict (Ω : Set ℝᵈ))) atTop (𝓝 0) := by
  obtain ⟨hM, hTB⟩ := th_Rellich_sousCritique Ω hΩb hΩ hp hpd hpstar hq
  obtain ⟨uLim, φ, hφ, hT, hL⟩ :=
    corolRellich_Lq Ω hΩb hp (hpd.trans (ENNReal.natCast_lt_top d)).ne hM hTB u hu
  exact ⟨uLim, φ, hφ, corolRellich_tendsto_weak.2 fun f => hT (f ∘L WithLp.sndL p ℝ _ _), hL⟩

/-- **Cor. `corol:Rellich` (Rellich, séquentiel), cas critique** (`p = d > 1`, `q ∈ [1, ∞[`).
Mêmes conclusions que le cas sous-critique.
Preuve (différente du cours) : extractions faibles composante par composante dans `L^p(Ω)`
(réflexif, de dual séparable) au lieu de la réflexivité de `W^{1,p}(Ω)` ; la limite est dans
`W^{1,p}(Ω)`, faiblement fermé ; une nouvelle extraction converge fortement par `th:Rellich`
(précompacité), et les deux limites coïncident p.p. (test contre les indicatrices).
Dépend des axiomes de Milman–Pettis et de Young faible. -/
theorem corol_Rellich_critique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : 1 < p) (hpd : p = d) (hq : q ≠ ∞)
    (u : ℕ → Sobolev1 Ω p) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ _ (u (φ n)).gradL) atTop
        (𝓝 (toWeakSpace ℝ _ uLim.gradL)) ∧
      Tendsto (fun n => eLpNorm (fun x => (u (φ n)).val x - uLim.val x) q
        (volume.restrict (Ω : Set ℝᵈ))) atTop (𝓝 0) := by
  obtain ⟨hM, hTB⟩ := th_Rellich_critique Ω hΩb hΩ hp hpd hq
  obtain ⟨uLim, φ, hφ, hT, hL⟩ :=
    corolRellich_Lq Ω hΩb hp (hpd ▸ ENNReal.natCast_ne_top d) hM hTB u hu
  exact ⟨uLim, φ, hφ, corolRellich_tendsto_weak.2 fun f => hT (f ∘L WithLp.sndL p ℝ _ _), hL⟩

/-- Cas sur-critique, avec la convergence faible exprimée composante par forme linéaire. -/
private lemma corolRellich_sur (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞)
    (u : ℕ → Sobolev1 Ω p) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ T : StrongDual ℝ (LpGrad Ω p),
        Tendsto (fun n => T (u (φ n) : LpGrad Ω p)) atTop (𝓝 (T (uLim : LpGrad Ω p)))) ∧
      ∃ (g : ℕ → C(closure (Ω : Set ℝᵈ), ℝ)) (gLim : C(closure (Ω : Set ℝᵈ), ℝ)),
        (∀ n, ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
          (u (φ n)).val x = g n ⟨x, hx⟩) ∧
        (∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
          uLim.val x = gLim ⟨x, hx⟩) ∧
        Tendsto g atTop (𝓝 gLim) := by
  classical
  obtain ⟨C, hC⟩ := hu
  have hΩm : MeasurableSet (Ω : Set ℝᵈ) := Ω.isOpen.measurableSet
  have : IsFiniteMeasure (volume.restrict (Ω : Set ℝᵈ)) :=
    isFiniteMeasure_restrict.2 hΩb.measure_lt_top.ne
  have : CompactSpace (closure (Ω : Set ℝᵈ)) :=
    isCompact_iff_compactSpace.1 hΩb.isCompact_closure
  obtain ⟨hM, hTB⟩ := th_Rellich_surCritique Ω hΩb hΩ hdp hp
  choose G hG using hM
  obtain ⟨uLim, φ₁, hφ₁, hT⟩ := corolRellich_weakSobolev Ω hp1 hp u C hC
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = max C 1 := ⟨_, rfl⟩
  have hc0 : 0 < c := hc_def ▸ lt_of_lt_of_le one_pos (le_max_right C 1)
  have hcu : ∀ n, ‖c⁻¹ • u n‖ ≤ 1 := by
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0, inv_mul_le_iff₀ hc0, mul_one,
      hc_def]
    exact (hC _).trans (le_max_left C 1)
  obtain ⟨z₀, φ₂, hφ₂, hz₀⟩ := corolRellich_seq_totallyBounded hTB
    (fun n => G (c⁻¹ • u (φ₁ n))) (fun n => ⟨c⁻¹ • u (φ₁ n), hcu _, hG _⟩)
  obtain ⟨g, hg_def⟩ : ∃ g : ℕ → C(closure (Ω : Set ℝᵈ), ℝ),
      g = fun n => c • G (c⁻¹ • u (φ₁ (φ₂ n))) := ⟨_, rfl⟩
  have hgrep : ∀ n, ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
      (u (φ₁ (φ₂ n))).val x = g n ⟨x, hx⟩ := by
    intro n
    filter_upwards [hG (c⁻¹ • u (φ₁ (φ₂ n))), Lp.coeFn_smul c⁻¹ (u (φ₁ (φ₂ n))).val]
      with x h1 h2 hx
    have h3 := h1 hx
    rw [corolRellich_val_smul, h2, Pi.smul_apply, smul_eq_mul] at h3
    rw [hg_def, ContinuousMap.smul_apply, smul_eq_mul, ← h3, mul_inv_cancel_left₀ hc0.ne']
  obtain ⟨gLim, hgLim⟩ : ∃ gLim : C(closure (Ω : Set ℝᵈ), ℝ), gLim = c • z₀ := ⟨_, rfl⟩
  have hgt : Tendsto g atTop (𝓝 gLim) := by
    rw [hg_def, hgLim]
    exact hz₀.const_smul c
  obtain ⟨F, hF_def⟩ : ∃ F : ℝᵈ → ℝ,
      F = fun x => if hx : x ∈ closure (Ω : Set ℝᵈ) then gLim ⟨x, hx⟩ else 0 := ⟨_, rfl⟩
  have hFc : ∀ x (hx : x ∈ closure (Ω : Set ℝᵈ)), F x = gLim ⟨x, hx⟩ := fun x hx => by
    simp [hF_def, hx]
  have hFm : MemLp F 1 (volume.restrict (Ω : Set ℝᵈ)) := by
    have hcont : ContinuousOn F (closure (Ω : Set ℝᵈ)) := by
      rw [continuousOn_iff_continuous_domRestrict]
      have : (closure (Ω : Set ℝᵈ)).domRestrict F = ⇑gLim :=
        funext fun x => hFc x.1 x.2
      rw [this]
      exact gLim.continuous
    refine MemLp.of_bound ((hcont.mono subset_closure).aestronglyMeasurable hΩm) ‖gLim‖ ?_
    filter_upwards [ae_restrict_mem hΩm] with x hx
    rw [hFc x (subset_closure hx)]
    exact gLim.norm_coe_le_norm _
  have hconv : Tendsto (fun n => eLpNorm (fun x => (u (φ₁ (φ₂ n))).val x - F x) 1
      (volume.restrict (Ω : Set ℝᵈ))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => volume.restrict (Ω : Set ℝᵈ) univ ^ (1 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal ‖g n - gLim‖) atTop (𝓝 0) := by
      have h0 := ENNReal.tendsto_ofReal (tendsto_iff_norm_sub_tendsto_zero.1 hgt)
      rw [ENNReal.ofReal_zero] at h0
      have := ENNReal.Tendsto.const_mul
        (a := volume.restrict (Ω : Set ℝᵈ) univ ^ (1 : ℝ≥0∞).toReal⁻¹) h0
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)))
      rwa [mul_zero] at this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) fun n => eLpNorm_le_of_ae_bound
        ((Lp.aestronglyMeasurable _).sub hFm.aestronglyMeasurable) ?_
    filter_upwards [hgrep n, ae_restrict_mem hΩm] with x h1 h2
    rw [h1 (subset_closure h2), hFc x (subset_closure h2), ← ContinuousMap.sub_apply]
    exact (g n - gLim).norm_coe_le_norm _
  have hid := corolRellich_ae_eq le_rfl (fun n => (u (φ₁ (φ₂ n))).val) uLim.val
    (fun T => (hT (T ∘L WithLp.fstL p ℝ _ _)).comp hφ₂.tendsto_atTop) hFm hconv
  refine ⟨uLim, φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun T => (hT T).comp hφ₂.tendsto_atTop, g, gLim, hgrep,
    ?_, hgt⟩
  filter_upwards [hid] with x hx hxc
  rw [hx, hFc x hxc]


/-- **Cor. `corol:Rellich` (Rellich, séquentiel), cas sur-critique** (`d < p < ∞`). Pour
toute suite `(u_n)` bornée dans `W^{1,p}(Ω)`, il existe `u_* ∈ W^{1,p}(Ω)` (`uLim`) et une
extractrice `φ` tels que `∇u_{φ(n)} ⇀ ∇u_*` faiblement dans `L^p(Ω)^d`, et `u_{φ(n)} → u_*`
dans `C(Ω̄)` : les représentants continus `g n` de `u_{φ(n)}` convergent uniformément vers un
représentant continu `gLim` de `u_*`.
Preuve (différente du cours) : extractions faibles composante par composante dans `L^p(Ω)`
(réflexif, de dual séparable) au lieu de la réflexivité de `W^{1,p}(Ω)` ; la limite est dans
`W^{1,p}(Ω)`, faiblement fermé ; une nouvelle extraction converge fortement par `th:Rellich`
(précompacité), et les deux limites coïncident p.p. (test contre les indicatrices).
Dépend de l'axiome de Milman–Pettis. -/
theorem corol_Rellich_surCritique (Ω : TopologicalSpace.Opens ℝᵈ)
    (hΩb : Bornology.IsBounded (Ω : Set ℝᵈ)) (hΩ : ProlongementSobolevTout Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hdp : (d : ℝ≥0∞) < p) (hp : p ≠ ∞)
    (u : ℕ → Sobolev1 Ω p) (hu : ∃ C, ∀ n, ‖u n‖ ≤ C) :
    ∃ (uLim : Sobolev1 Ω p) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun n => toWeakSpace ℝ _ (u (φ n)).gradL) atTop
        (𝓝 (toWeakSpace ℝ _ uLim.gradL)) ∧
      ∃ (g : ℕ → C(closure (Ω : Set ℝᵈ), ℝ)) (gLim : C(closure (Ω : Set ℝᵈ), ℝ)),
        (∀ n, ∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
          (u (φ n)).val x = g n ⟨x, hx⟩) ∧
        (∀ᵐ x ∂(volume.restrict (Ω : Set ℝᵈ)), ∀ hx : x ∈ closure (Ω : Set ℝᵈ),
          uLim.val x = gLim ⟨x, hx⟩) ∧
        Tendsto g atTop (𝓝 gLim) := by
  obtain ⟨uLim, φ, hφ, hT, hg⟩ := corolRellich_sur Ω hΩb hΩ hp1 hdp hp u hu
  exact ⟨uLim, φ, hφ, corolRellich_tendsto_weak.2 fun f => hT (f ∘L WithLp.sndL p ℝ _ _), hg⟩
end M1Analyse
