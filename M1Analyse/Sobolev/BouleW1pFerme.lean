/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.Rellich

/-!
# §5.5 Fermeture dans `L^q` de la boule unité de `W^{1,p}` (`rem:bouleW1pFerme`)

Source : `Include/Sobolev.tex`, `rem:bouleW1pFerme`. Deux énoncés : `1 < p < ∞` et `p = ∞`.
Ni la régularité de `Ω`, ni l'inclusion continue `W^{1,p}(Ω) ⊂ L^q(Ω)` ne sont nécessaires
(\claudereport) : l'énoncé Lean vaut pour tout ouvert `Ω` et tout `q ∈ [1, ∞]`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Distributions LineDeriv

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Une fonction test est dans `L^q(Ω)` pour tout `q`. -/
private lemma bouleW1p_memLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) (φ : 𝓓(Ω, ℝ)) :
    MemLp φ q (volume.restrict (Ω : Set ℝᵈ)) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- `L^p(Ω) ⊆ L^1_loc(Ω)` pour `p ≥ 1`. -/
private lemma bouleW1p_locInt {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) : LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)

private lemma bouleW1p_ofFun_apply {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) (ψ : 𝓓(Ω, ℝ)) :
    Distribution.ofFun Ω (f : ℝᵈ → ℝ) volume ⊤ ψ = ∫ x in (Ω : Set ℝᵈ), f x * ψ x := by
  rw [Distribution.ofFun_apply (bouleW1p_locInt f),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [smul_eq_mul, mul_comm]
  · intro x hx
    simp [ψ.zero_on_compl hx]

/-- L'injection linéaire `𝓓(Ω) → L^q(Ω)`. -/
private noncomputable def bouleW1p_toLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞)
    [Fact (1 ≤ q)] : 𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) where
  toFun φ := (bouleW1p_memLp Ω q φ).toLp φ
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    rfl

private lemma bouleW1p_toLp_coe (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (φ : 𝓓(Ω, ℝ)) : (bouleW1p_toLp Ω q φ : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] φ :=
  MemLp.coeFn_toLp (bouleW1p_memLp Ω q φ)

/-- Dérivée partielle `∂ᵢ : 𝓓(Ω) → 𝓓(Ω)`. -/
private noncomputable def bouleW1p_partial (Ω : TopologicalSpace.Opens ℝᵈ) (i : Fin d) :
    𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ))

/-- Caractérisation faible : `u ∈ W^{1,p}(Ω)` ssi `∫ u ∂ᵢψ + ∫ gᵢ ψ = 0` pour toute `ψ`. -/
private lemma bouleW1p_mem_iff {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : LpGrad Ω p) : u ∈ W1p Ω p ↔ ∀ (i : Fin d) (ψ : 𝓓(Ω, ℝ)),
      (∫ x in (Ω : Set ℝᵈ), u.fst x * bouleW1p_partial Ω i ψ x) +
        ∫ x in (Ω : Set ℝᵈ), u.snd i x * ψ x = 0 := by
  rw [mem_W1p]
  refine forall_congr' fun i => ?_
  rw [DFunLike.ext_iff]
  refine forall_congr' fun ψ => ?_
  rw [Distribution.lineDerivOp_eq_lineDerivCLM, Distribution.lineDerivCLM_apply,
    bouleW1p_ofFun_apply, bouleW1p_ofFun_apply, neg_eq_iff_add_eq_zero]
  rfl

/-- Pairing `f ↦ ∫_Ω f ψ` continu sur `L^p(Ω)`, pour `ψ` fonction test. -/
private lemma bouleW1p_continuous_pairing (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (ψ : 𝓓(Ω, ℝ)) :
    Continuous fun f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) =>
      ∫ x in (Ω : Set ℝᵈ), f x * ψ x := by
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have h : ∀ f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)),
      ∫ x in (Ω : Set ℝᵈ), f x * ψ x =
        ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume.restrict (Ω : Set ℝᵈ)) p
          p.conjExponent).flip (bouleW1p_toLp Ω p.conjExponent ψ) f := by
    intro f
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ((bouleW1p_toLp_coe Ω p.conjExponent ψ).mono fun x hx => ?_)
    simp [hx]
  simp_rw [h]
  exact ContinuousLinearMap.continuous _

/-- Une suite de formes `L n` de normes `≤ c n → a`, convergeant simplement sur un sous-espace
`D`, admet une limite sur `D` prolongée (Hahn–Banach) en une forme de norme `≤ a`. -/
private lemma bouleW1p_extend {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℕ → StrongDual ℝ E) (D : Submodule ℝ E) {c : ℕ → ℝ} {a : ℝ}
    (hL : ∀ n, ‖L n‖ ≤ c n) (hc : Tendsto c atTop (𝓝 a))
    (hD : ∀ x ∈ D, ∃ l, Tendsto (fun n => L n x) atTop (𝓝 l)) :
    ∃ Λ : StrongDual ℝ E, ‖Λ‖ ≤ a ∧ ∀ x ∈ D, Tendsto (fun n => L n x) atTop (𝓝 (Λ x)) := by
  have hlim : ∀ x : D, Tendsto (fun n => L n x) atTop (𝓝 (limUnder atTop fun n => L n x)) :=
    fun x => tendsto_nhds_limUnder (hD x x.2)
  let T : D →ₗ[ℝ] ℝ :=
    { toFun := fun x => limUnder atTop fun n => L n x
      map_add' := fun x y => by
        refine tendsto_nhds_unique (hlim (x + y)) ?_
        simpa using (hlim x).add (hlim y)
      map_smul' := fun r x => by
        refine tendsto_nhds_unique (hlim (r • x)) ?_
        simpa using (hlim x).const_mul r }
  have ha : 0 ≤ a := ge_of_tendsto' hc fun n => (norm_nonneg _).trans (hL n)
  have hT : ∀ x : D, ‖T x‖ ≤ a * ‖x‖ := by
    intro x
    have h1 : Tendsto (fun n => ‖L n x‖) atTop (𝓝 ‖T x‖) := (hlim x).norm
    have h2 : Tendsto (fun n => c n * ‖x‖) atTop (𝓝 (a * ‖x‖)) := hc.mul_const _
    refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
    exact ((L n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hL n) (norm_nonneg _))
  obtain ⟨Λ, hΛ, hΛn⟩ := exists_extension_norm_eq D (T.mkContinuous a hT)
  refine ⟨Λ, hΛn ▸ LinearMap.mkContinuous_norm_le _ ha _, fun x hx => ?_⟩
  convert hlim ⟨x, hx⟩ using 2
  exact hΛ ⟨x, hx⟩

/-- Limite faible d'une composante : si `∫ hₙ ψ → T ψ` pour toute fonction test `ψ` et
`‖hₙ‖_p → a`, alors `T ψ = ∫ g ψ` pour un `g ∈ L^p(Ω)` avec `‖g‖_p ≤ a` (dualité
`L^p = (L^{p'})^*`, supposée via `hsurj`, `hiso`). -/
private lemma bouleW1p_weakLim (Ω : TopologicalSpace.Opens ℝᵈ) {p p' : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ p')] [p.HolderConjugate p']
    (hsurj : Function.Surjective (dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p))
    (hiso : Isometry (dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p))
    (h : ℕ → Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) {a : ℝ}
    (ha : Tendsto (fun n => ‖h n‖) atTop (𝓝 a)) (T : 𝓓(Ω, ℝ) → ℝ)
    (hT : ∀ ψ, Tendsto (fun n => ∫ x in (Ω : Set ℝᵈ), h n x * ψ x) atTop (𝓝 (T ψ))) :
    ∃ g : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)), ‖g‖ ≤ a ∧
      ∀ ψ : 𝓓(Ω, ℝ), ∫ x in (Ω : Set ℝᵈ), g x * ψ x = T ψ := by
  have hpair : ∀ (g : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) (ψ : 𝓓(Ω, ℝ)),
      dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p g (bouleW1p_toLp Ω p' ψ) =
        ∫ x in (Ω : Set ℝᵈ), g x * ψ x := by
    intro g ψ
    rw [dualLp_apply]
    refine integral_congr_ae ((bouleW1p_toLp_coe Ω p' ψ).mono fun x hx => ?_)
    simp only [hx, mul_comm]
  have hnorm : ∀ g : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)),
      ‖dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p g‖ = ‖g‖ :=
    hiso.norm_map_of_map_zero (map_zero _)
  obtain ⟨Λ, hΛ, hlim⟩ :=
    bouleW1p_extend (fun n => dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p (h n))
    (LinearMap.range (bouleW1p_toLp Ω p')) (fun n => (hnorm (h n)).le) ha (by
      rintro _ ⟨ψ, rfl⟩
      exact ⟨T ψ, by simpa only [hpair] using hT ψ⟩)
  obtain ⟨g, rfl⟩ := hsurj Λ
  refine ⟨g, by rw [← hnorm]; exact hΛ, fun ψ => ?_⟩
  rw [← hpair]
  refine tendsto_nhds_unique (hlim _ ⟨ψ, rfl⟩) ?_
  simpa only [hpair] using hT ψ

/-- Passage à la limite : si `Fₙ = uₙ` p.p., `Fₙ → f` dans `L^q(Ω)`, et les normes des
composantes de `uₙ ∈ W^{1,p}(Ω)` convergent vers `a`, `bᵢ`, alors `f = w` p.p. pour un
`w ∈ W^{1,p}(Ω)` avec `‖w‖_p ≤ a` et `‖∂ᵢw‖_p ≤ bᵢ`. -/
private lemma bouleW1p_limit (Ω : TopologicalSpace.Opens ℝᵈ) {p p' q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ p')] [Fact (1 ≤ q)] [p.HolderConjugate p']
    (hsurj : Function.Surjective (dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p))
    (hiso : Isometry (dualLp (volume.restrict (Ω : Set ℝᵈ)) p' p))
    (u : ℕ → Sobolev1 Ω p) (F : ℕ → Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)))
    (f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ))) (hF : Tendsto F atTop (𝓝 f))
    (hae : ∀ n, (F n : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] (u n).val)
    {a : ℝ} {b : Fin d → ℝ} (ha : Tendsto (fun n => ‖(u n).val‖) atTop (𝓝 a))
    (hb : ∀ i, Tendsto (fun n => ‖(u n).grad i‖) atTop (𝓝 (b i))) :
    ∃ w : Sobolev1 Ω p, ‖w.val‖ ≤ a ∧ (∀ i, ‖w.grad i‖ ≤ b i) ∧
      (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] w.val := by
  have hval : ∀ φ : 𝓓(Ω, ℝ), Tendsto (fun n => ∫ x in (Ω : Set ℝᵈ), (u n).val x * φ x)
      atTop (𝓝 (∫ x in (Ω : Set ℝᵈ), f x * φ x)) := by
    intro φ
    refine (((bouleW1p_continuous_pairing Ω q φ).tendsto f).comp hF).congr fun n => ?_
    refine integral_congr_ae ((hae n).mono fun x hx => ?_)
    simp only [hx]
  obtain ⟨v, hv, hvf⟩ := bouleW1p_weakLim Ω hsurj hiso _ ha _ hval
  have hgrad : ∀ (i : Fin d) (φ : 𝓓(Ω, ℝ)),
      Tendsto (fun n => ∫ x in (Ω : Set ℝᵈ), (u n).grad i x * φ x) atTop
        (𝓝 (-∫ x in (Ω : Set ℝᵈ), f x * bouleW1p_partial Ω i φ x)) := by
    intro i φ
    refine (hval (bouleW1p_partial Ω i φ)).neg.congr fun n => ?_
    have h0 : (∫ x in (Ω : Set ℝᵈ), (u n).val x * bouleW1p_partial Ω i φ x) +
        ∫ x in (Ω : Set ℝᵈ), (u n).grad i x * φ x = 0 := (bouleW1p_mem_iff _).1 (u n).2 i φ
    linarith
  choose g hg hgf using fun i => bouleW1p_weakLim Ω hsurj hiso _ (hb i) _ (hgrad i)
  refine ⟨⟨WithLp.toLp p (v, WithLp.toLp p g), ?_⟩, hv, hg, ?_⟩
  · rw [bouleW1p_mem_iff]
    intro i φ
    have h0 : (∫ x in (Ω : Set ℝᵈ), v x * bouleW1p_partial Ω i φ x) +
        ∫ x in (Ω : Set ℝᵈ), g i x * φ x = 0 := by
      rw [hgf, hvf]
      ring
    exact h0
  · refine prop_distribL1Loc_injective Ω (bouleW1p_locInt f) (bouleW1p_locInt v) ?_
    ext φ
    rw [bouleW1p_ofFun_apply, bouleW1p_ofFun_apply]
    exact (hvf φ).symm

/-- Extraction d'une sous-suite le long de laquelle les normes des composantes convergent. -/
private lemma bouleW1p_subseq {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : ℕ → Sobolev1 Ω p) (hu : ∀ n, ‖u n‖ ≤ 1) :
    ∃ (φ : ℕ → ℕ) (a : ℝ) (b : Fin d → ℝ), StrictMono φ ∧
      Tendsto (fun n => ‖(u (φ n)).val‖) atTop (𝓝 a) ∧
      ∀ i, Tendsto (fun n => ‖(u (φ n)).grad i‖) atTop (𝓝 (b i)) := by
  have hval : ∀ n, ‖(u n).val‖ ≤ 1 := fun n => (WithLp.norm_fst_le (x := _)).trans (hu n)
  have hgrad : ∀ n i, ‖(u n).grad i‖ ≤ 1 := fun n i =>
    ((PiLp.norm_apply_le _ i).trans (WithLp.norm_snd_le (x := _))).trans (hu n)
  obtain ⟨c, -, φ, hφ, hlim⟩ := (isCompact_Icc (a := ((0 : ℝ), fun _ : Fin d => (0 : ℝ)))
    (b := (1, fun _ => 1))).tendsto_subseq
    (x := fun n => (‖(u n).val‖, fun i => ‖(u n).grad i‖))
    fun n => ⟨⟨norm_nonneg _, fun _ => norm_nonneg _⟩, ⟨hval n, fun i => hgrad n i⟩⟩
  exact ⟨φ, c.1, c.2, hφ, (continuous_fst.tendsto c).comp hlim, fun i =>
    ((continuous_apply i).tendsto c.2).comp ((continuous_snd.tendsto c).comp hlim)⟩

/-- **Rem. `rem:bouleW1pFerme` (Fermeture dans `L^q` de la boule unité de `W^{1,p}`).** Soient
`Ω` un ouvert, `p ∈ ]1, ∞[` et `q ∈ [1, ∞]`. Alors l'ensemble des `f ∈ L^q(Ω)` égales p.p. à
un `u ∈ W^{1,p}(Ω)` de norme `≤ 1` est fermé dans `L^q(Ω)`.
Preuve (différente du cours) : pas de réflexivité de `W^{1,p}(Ω)` ni d'extraction faible.
Si `u_n → f` dans `L^q` avec `‖u_n‖ ≤ 1`, on extrait seulement une sous-suite des normes
`‖u_n‖_p`, `‖∂ᵢu_n‖_p` (nombres réels bornés). La limite de `∫ u_n ψ` (resp. de `∫ ∂ᵢu_n ψ`)
est connue pour `ψ ∈ 𝓓(Ω)` grâce à la convergence forte ; ces formes linéaires, bornées pour la
norme `L^{p'}` par la limite des normes, se prolongent par Hahn–Banach et sont représentées
par dualité `L^p = (L^{p'})^*` (`th:lpDualLq`), ce qui fournit `u ∈ W^{1,p}(Ω)`, `‖u‖ ≤ 1`.
Dépend de l'axiome de Milman–Pettis (via `th_lpDualLq_bijectif`). -/
theorem rem_bouleW1pFerme (Ω : TopologicalSpace.Opens ℝᵈ) {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    [Fact (1 ≤ q)] (hp : 1 < p) (hp' : p ≠ ∞) :
    IsClosed {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω p, ‖u‖ ≤ 1 ∧
      (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val} := by
  have hp1 : 1 < p.conjExponent := by
    rw [ENNReal.conjExponent]
    exact ENNReal.lt_add_right ENNReal.one_ne_top
      (ENNReal.inv_ne_zero.2 (ENNReal.sub_ne_top hp'))
  have hp2 : p.conjExponent ≠ ∞ := by
    rw [ENNReal.conjExponent]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top,
      ENNReal.inv_ne_top.2 (tsub_pos_of_lt hp).ne'⟩
  have : Fact (1 ≤ p.conjExponent) := ⟨hp1.le⟩
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  choose u hu hae using hFS
  obtain ⟨φ, a, b, hφ, ha, hb⟩ := bouleW1p_subseq u hu
  obtain ⟨w, hwv, hwg, hfw⟩ := bouleW1p_limit Ω (th_lpDualLq_bijectif hp1 hp2).2
    (th_lpDualLq_isometrie fun h => absurd h hp1.ne') (u ∘ φ) (F ∘ φ) f
    (hF.comp hφ.tendsto_atTop) (fun n => hae (φ n)) ha hb
  refine ⟨w, ?_, hfw⟩
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans hp).ne' hp'
  have hlimN : Tendsto (fun n => ‖u (φ n)‖ ^ p.toReal) atTop
      (𝓝 (a ^ p.toReal + ∑ i, b i ^ p.toReal)) := by
    simp_rw [norm_W1p hp']
    exact (ha.rpow_const (Or.inr hp0.le)).add
      (tendsto_finsetSum _ fun i _ => (hb i).rpow_const (Or.inr hp0.le))
  have hle : a ^ p.toReal + ∑ i, b i ^ p.toReal ≤ 1 :=
    le_of_tendsto' hlimN fun n => Real.rpow_le_one (norm_nonneg _) (hu _) hp0.le
  have hw : ‖w‖ ^ p.toReal ≤ 1 := by
    rw [norm_W1p hp']
    refine le_trans (add_le_add ?_ (Finset.sum_le_sum fun i _ => ?_)) hle
    · exact Real.rpow_le_rpow (norm_nonneg _) hwv hp0.le
    · exact Real.rpow_le_rpow (norm_nonneg _) (hwg i) hp0.le
  by_contra hcon
  exact absurd hw (not_le.2 (Real.one_lt_rpow (not_le.1 hcon) hp0))

/-- **Rem. `rem:bouleW1pFerme`, cas `p = ∞`.** Pour tout ouvert `Ω` et `q ∈ [1, ∞]`,
l'ensemble des `f ∈ L^q(Ω)` égales p.p. à un `u ∈ W^{1,∞}(Ω)` de norme `≤ 1` est fermé.
Preuve (différente du cours) : pas de réflexivité de `W^{1,p}(Ω)` ni d'extraction faible.
Si `u_n → f` dans `L^q` avec `‖u_n‖ ≤ 1`, on extrait seulement une sous-suite des normes
`‖u_n‖_p`, `‖∂ᵢu_n‖_p` (nombres réels bornés). La limite de `∫ u_n ψ` (resp. de `∫ ∂ᵢu_n ψ`)
est connue pour `ψ ∈ 𝓓(Ω)` grâce à la convergence forte ; ces formes linéaires, bornées pour la
norme `L^{p'}` par la limite des normes, se prolongent par Hahn–Banach et sont représentées
par dualité `L^∞ = (L^1)^*` (`th_lpDualLq_bijectif_un`). `W^{1,∞}(Ω)` n'étant pas réflexif, la
preuve du cours ne s'applique pas ici. -/
theorem rem_bouleW1pFerme_top (Ω : TopologicalSpace.Opens ℝᵈ) {q : ℝ≥0∞} [Fact (1 ≤ q)] :
    IsClosed {f : Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) | ∃ u : Sobolev1 Ω ∞, ‖u‖ ≤ 1 ∧
      (f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val} := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨F, hFS, hF⟩ := mem_closure_iff_seq_limit.1 hf
  choose u hu hae using hFS
  obtain ⟨φ, a, b, hφ, ha, hb⟩ := bouleW1p_subseq u hu
  obtain ⟨w, hwv, hwg, hfw⟩ := bouleW1p_limit Ω (p' := 1) th_lpDualLq_bijectif_un.2
    (th_lpDualLq_isometrie fun _ => inferInstance) (u ∘ φ) (F ∘ φ) f
    (hF.comp hφ.tendsto_atTop) (fun n => hae (φ n)) ha hb
  refine ⟨w, ?_, hfw⟩
  rw [norm_W1p_top]
  refine max_le (hwv.trans (le_of_tendsto' ha fun n => ?_))
    (Real.iSup_le (fun i => (hwg i).trans (le_of_tendsto' (hb i) fun n => ?_)) zero_le_one)
  · exact (WithLp.norm_fst_le (x := _)).trans (hu _)
  · exact ((PiLp.norm_apply_le _ i).trans (WithLp.norm_snd_le (x := _))).trans (hu _)

end M1Analyse
