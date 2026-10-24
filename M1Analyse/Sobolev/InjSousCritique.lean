/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import M1Analyse.Sobolev.ConvolutionLp

/-!
# §5.3 Injections de Sobolev - cas sous-critique (`subsec:injSousCrit`)

Source : `Include/Sobolev.tex`, sous-section `subsec:injSousCrit`.

Les espaces `L^p` du cours sont ceux de Mathlib (`MemLp`, `eLpNorm`), la convolution est
`MeasureTheory.convolution` (`f ⋆ g = f ⋆[lsmul ℝ ℝ, volume] g`, de formule
`(f ⋆ g)(x) = ∫ f(h) g(x - h) dh`), et `ℝ^d` est `EuclideanSpace ℝ (Fin d)` muni de la mesure
de Lebesgue `volume`. La quasi-norme faible `‖·‖_{p,w}`, absente de Mathlib, est introduite
(`normeFaible`) avec sa formule littérale.

La proposition `prop:convolPow` est formalisée dans `M1Analyse/Sobolev/NoyauGreen.lean`
(`prop_convolPow`). Ne sont pas formalisés : `th:YoungFaible` (admis dans le cours),
`th:injSousCrit` et `corol:injSousCritOm` (les espaces de Sobolev `W^{s,p}` ne sont pas dans
Mathlib), ni la seconde identité de `eq:homog_lp` (dérivées).
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Convolution
open ContinuousLinearMap (lsmul)

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-! ### Espace `L^p` faible -/

/-- Quasi-norme `L^p` faible du cours (`subsec:injSousCrit`) : pour `(X, μ)` un espace mesuré,
`f : X → ℝ` et `p ∈ [1, ∞[`, `‖f‖_{p,w}^p := sup_{t > 0} μ{|f| ≥ t} t^p`, c'est-à-dire
`‖f‖_{p,w} := (sup_{t > 0} μ{|f| ≥ t} t^p)^{1/p}` (à valeurs dans `[0, ∞]`). L'espace faible
est `L^{p,w} := {f mesurable | ‖f‖_{p,w} < ∞}`. Cette notion n'est pas dans Mathlib. -/
noncomputable def normeFaible {X : Type*} [MeasurableSpace X] (μ : Measure X) (p : ℝ)
    (f : X → ℝ) : ℝ≥0∞ :=
  (⨆ (t : ℝ) (_ : 0 < t), μ {x | t ≤ |f x|} * ENNReal.ofReal (t ^ p)) ^ (1 / p)

/-- **`‖f‖_{p,w} ≤ ‖f‖_p`** (énoncé non numéroté de `subsec:injSousCrit`). Pour tout espace
mesuré `(X, μ)`, `f : X → ℝ` et `p ∈ [1, ∞[`, la quasi-norme faible est majorée par la norme
`L^p` (inégalité de Markov). Remarque : vrai sans hypothèse de mesurabilité, car
`eLpNorm f p μ = ∞` dans Mathlib si `f` n'est pas (presque) mesurable. -/
theorem normeFaible_le_eLpNorm {X : Type*} [MeasurableSpace X] (μ : Measure X) {p : ℝ}
    (hp : 1 ≤ p) (f : X → ℝ) : normeFaible μ p f ≤ eLpNorm f (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have key : (⨆ (t : ℝ) (_ : 0 < t), μ {x | t ≤ |f x|} * ENNReal.ofReal (t ^ p)) ≤
      eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    refine iSup₂_le fun t ht => ?_
    have := mul_meas_ge_le_pow_eLpNorm' (μ := μ) (f := f) (by simpa using hp0)
      ENNReal.ofReal_ne_top (ENNReal.ofReal t)
    rw [hpr] at this
    convert this using 1
    rw [mul_comm, ENNReal.ofReal_rpow_of_nonneg ht.le hp0.le]
    congr 2
    ext x
    simp [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)]
  unfold normeFaible
  calc _ ≤ (eLpNorm f (ENNReal.ofReal p) μ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow key (by positivity)
    _ = _ := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **Éq. `eq:powLpw`.** Pour `0 < α ≤ d`, la fonction `x ↦ 1 / |x|^α` est dans
`L^{d/α, w}(ℝ^d)` : elle est mesurable et `‖1/|x|^α‖_{d/α, w} < ∞`. (En `x = 0`, la valeur
`1 / 0 = 0` de Lean est sans importance.) On a en fait `μ{1/|x|^α ≥ t} t^{d/α} ≤ |B(0,1)|`. -/
theorem eq_powLpw {α : ℝ} (hα : 0 < α) (hαd : α ≤ d) :
    Measurable (fun x : ℝᵈ => 1 / ‖x‖ ^ α) ∧
      normeFaible volume (d / α) (fun x : ℝᵈ => 1 / ‖x‖ ^ α) < ∞ := by
  refine ⟨by fun_prop, ?_⟩
  have hd : (0 : ℝ) < d := hα.trans_le hαd
  have key : ∀ t : ℝ, 0 < t → volume {x : ℝᵈ | t ≤ |1 / ‖x‖ ^ α|} * ENNReal.ofReal (t ^ (d / α))
      ≤ volume (ball (0 : ℝᵈ) 1) := by
    intro t ht
    have hsub : {x : ℝᵈ | t ≤ |1 / ‖x‖ ^ α|} ⊆ closedBall 0 ((t⁻¹) ^ (1 / α)) := by
      intro x hx
      simp only [mem_ofPred_eq] at hx
      rw [mem_closedBall, dist_zero_right]
      have hx0 : 0 < ‖x‖ := by
        rcases (norm_nonneg x).eq_or_lt with h | h
        · rw [← h, Real.zero_rpow hα.ne'] at hx
          simp at hx
          linarith
        · exact h
      rw [abs_of_pos (by positivity), le_div_iff₀ (by positivity), ← le_div_iff₀' ht,
        one_div] at hx
      calc ‖x‖ = (‖x‖ ^ α) ^ (1 / α) := by
            rw [← Real.rpow_mul hx0.le, mul_one_div_cancel hα.ne', Real.rpow_one]
        _ ≤ (t⁻¹) ^ (1 / α) := Real.rpow_le_rpow (by positivity) hx (by positivity)
    calc volume {x : ℝᵈ | t ≤ |1 / ‖x‖ ^ α|} * ENNReal.ofReal (t ^ (d / α))
        ≤ volume (closedBall (0 : ℝᵈ) ((t⁻¹) ^ (1 / α))) * ENNReal.ofReal (t ^ (d / α)) := by
          gcongr
      _ = volume (ball (0 : ℝᵈ) 1) := by
          rw [Measure.addHaar_closedBall _ _ (by positivity), finrank_euclideanSpace_fin,
            mul_comm, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          have : t ^ (d / α) * ((t⁻¹) ^ (1 / α)) ^ d = 1 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow ht.le,
              ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
            have : d / α + -(1 / α * d) = 0 := by ring
            rw [this, Real.rpow_zero]
          rw [this, ENNReal.ofReal_one, one_mul]
  unfold normeFaible
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_
  exact ((iSup₂_le key).trans_lt measure_ball_lt_top).ne

/-! ### Homogénéité -/

/-- **Éq. `eq:homog_lp` (Homogénéité, remarque `rem:homogSobolev`), première identité.** Pour
`u : ℝ^d → ℝ`, `p ∈ [1, ∞]` et `λ > 0` (noté `c`), la fonction `u_λ(x) := u(λ x)` vérifie
`‖u_λ‖_p = λ^{-d/p} ‖u‖_p` (avec `d/∞ = 0`; dans Lean, `p.toReal = 0` si `p = ∞` et `x / 0 = 0`).
Remarque : le cours suppose `u ∈ 𝒟(ℝ^d)` ; l'identité vaut pour toute fonction `u` et tout
exposant `p`. La seconde identité (dérivées `∂_α u_λ`) est `eq_homog_lp_deriv`. -/
theorem eq_homog_lp (u : ℝᵈ → ℝ) (p : ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    eLpNorm (fun x => u (c • x)) p = ENNReal.ofReal (c ^ (-(d : ℝ) / p.toReal)) * eLpNorm u p := by
  have h1 : (fun x => u (c • x)) = u ∘ (MeasurableEquiv.smul₀ c hc.ne' : ℝᵈ ≃ᵐ ℝᵈ) := rfl
  rw [h1, ← (MeasurableEquiv.smul₀ c hc.ne' : ℝᵈ ≃ᵐ ℝᵈ).measurableEmbedding.eLpNorm_map_measure,
    MeasurableEquiv.coe_smul₀, Measure.map_addHaar_smul volume hc.ne',
    eLpNorm_smul_measure_of_ne_zero (by simp [hc.ne'])]
  rw [smul_eq_mul, finrank_euclideanSpace_fin, ENNReal.ofReal_rpow_of_nonneg (by positivity)
    (by positivity)]
  congr 2
  rw [abs_of_pos (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hc.le, ← Real.rpow_mul hc.le,
    one_div, ENNReal.toReal_inv]
  rw [div_eq_mul_inv]

/-- Dérivée partielle d'une fonction dilatée (`rem:homogSobolev`) : pour `c ≠ 0`, un
multi-indice `α` et `s := |α|₁ = ∑ i, α i`, on a `∂_α (x ↦ u(c x))(x) = c^s ∂_α u(c x)`.
Remarque : aucune hypothèse de régularité sur `u` n'est requise (`x ↦ c x` est un isomorphisme
linéaire continu, et Mathlib ne demande aucune différentiabilité pour composer à droite par un
tel isomorphisme ; si `u` n'est pas dérivable, les deux membres sont nuls). -/
theorem deriveePartielle_comp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : Fin d → ℕ) (u : ℝᵈ → F) {c : ℝ} (hc : c ≠ 0) (x : ℝᵈ) :
    deriveePartielle α (fun y => u (c • y)) x = c ^ (∑ i, α i) • deriveePartielle α u (c • x) := by
  let g : ℝᵈ ≃L[ℝ] ℝᵈ :=
    (LinearEquiv.smulOfNeZero ℝ ℝᵈ c hc).toContinuousLinearEquiv
  have hg : ∀ y, g y = c • y := fun _ => rfl
  have h := g.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ (g x))
    (directions α).length
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h
  have hfun : (fun y => u (c • y)) = u ∘ g := rfl
  rw [deriveePartielle, deriveePartielle, hfun, h,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, hg]
  rw [ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  rw [length_directions]

/-- **Éq. `eq:homog_lp` (Homogénéité), seconde identité.** Pour `u : ℝ^d → ℝ`, `p ∈ [1, ∞]`,
un multi-indice `α ∈ ℕ^d` de longueur `s := |α|₁` et `λ > 0` (noté `c`), la fonction
`u_λ(x) := u(λ x)` vérifie `‖∂_α u_λ‖_p = λ^{s - d/p} ‖∂_α u‖_p` (avec `d/∞ = 0` ; dans Lean,
`p.toReal = 0` si `p = ∞` et `x / 0 = 0`).
Remarque : le cours suppose `u ∈ 𝒟(ℝ^d)` ; l'identité vaut pour toute fonction `u`, sans
hypothèse de régularité, et tout exposant `p` (cf. `deriveePartielle_comp_smul`). -/
theorem eq_homog_lp_deriv (u : ℝᵈ → ℝ) (α : Fin d → ℕ) (p : ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    eLpNorm (deriveePartielle α (fun x => u (c • x))) p =
      ENNReal.ofReal (c ^ ((∑ i, α i : ℕ) - (d : ℝ) / p.toReal)) *
        eLpNorm (deriveePartielle α u) p := by
  have h1 : deriveePartielle α (fun x => u (c • x)) =
      c ^ (∑ i, α i) • fun x => deriveePartielle α u (c • x) := by
    ext x
    simp [deriveePartielle_comp_smul α u hc.ne' x]
  rw [h1, eLpNorm_const_smul, eq_homog_lp _ p hc, ← mul_assoc,
    Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_add hc, sub_eq_add_neg, neg_div]

/-! ### Inégalité de Young -/

/-- Inégalité de Hölder (`th:HolderIneq`) pour des fonctions positives `a, b : X → [0, ∞]`
et des exposants conjugués `p, q ∈ [1, ∞]` : `∫ a b ≤ ‖a‖_p ‖b‖_q`. -/
theorem lintegral_mul_le_eLpNorm_mul_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p q : ℝ≥0∞} [hpq : p.HolderConjugate q] {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ)
    (hb : AEMeasurable b μ) :
    ∫⁻ x, a x * b x ∂μ ≤ eLpNorm a p μ * eLpNorm b q μ := by
  have key : ∀ a b : α → ℝ≥0∞, AEMeasurable a μ → AEMeasurable b μ →
      ∫⁻ x, a x * b x ∂μ ≤ eLpNorm a ∞ μ * eLpNorm b 1 μ := by
    intro a b ha hb
    rw [eLpNorm_exponent_top ha.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hb.aestronglyMeasurable]
    simp only [enorm_eq_self]
    rw [← lintegral_const_mul'' _ hb]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_le_eLpNormEssSup (f := a) (μ := μ)] with x hx
    simp only [enorm_eq_self] at hx
    exact mul_le_mul_left hx _
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ q).1 rfl
    exact key a b ha hb
  rcases eq_or_ne q ∞ with rfl | hq
  · obtain rfl : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ p).1 rfl
    rw [mul_comm]
    simpa only [mul_comm (b _)] using key b a hb ha
  have hr := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hr ha hb
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.HolderConjugate.ne_zero p q) hp
      ha.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.HolderConjugate.ne_zero q p) hq
      hb.aestronglyMeasurable]
  simpa only [enorm_eq_self, Pi.mul_apply] using h

/-- Fubini–Tonelli et invariance par translation : `∫∫ f(y) g(x - y) dy dx = ∫ f ∫ g`. -/
theorem lintegral_lintegral_mul_sub {f g : ℝᵈ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) :
    ∫⁻ x, ∫⁻ y, f y * g (x - y) = (∫⁻ y, f y) * ∫⁻ y, g y := by
  have hK : AEMeasurable (Function.uncurry fun x y => f y * g (x - y))
      (volume.prod volume) :=
    (hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  rw [lintegral_lintegral_swap hK, ← lintegral_mul_const'' _ hf]
  refine lintegral_congr fun y => ?_
  rw [lintegral_const_mul'' (f y) (f := fun x => g (x - y)) ((hg.comp_quasiMeasurePreserving
    (measurePreserving_sub_right volume y).quasiMeasurePreserving)),
    lintegral_sub_right_eq_self g y]

/-- Estimation clé (fonctions positives, exposants finis) : si `P, Q, S ≥ 1` et
`1/P + 1/Q = 1 + 1/S`, alors
`∫ (∫ f(y) g(x - y) dy)^S dx ≤ (∫ f^P)^{S/P} (∫ g^Q)^{S/Q}`.
Preuve : inégalité de Hölder à trois facteurs en `y`, écrivant
`f g = (f^P g^Q)^{1/S} (f^P)^{1/P - 1/S} (g^Q)^{1/Q - 1/S}`, puis Fubini–Tonelli. -/
theorem lintegral_conv_rpow_le {P Q S : ℝ} (hP : 1 ≤ P) (hQ : 1 ≤ Q) (hS : 1 ≤ S)
    (h : P⁻¹ + Q⁻¹ = 1 + S⁻¹) {f g : ℝᵈ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) :
    ∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ S ≤
      (∫⁻ y, f y ^ P) ^ (S / P) * (∫⁻ y, g y ^ Q) ^ (S / Q) := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hPi : P⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hP
  have hQi : Q⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hQ
  set A := ∫⁻ y, f y ^ P with hA
  set B := ∫⁻ y, g y ^ Q with hB
  set a := S⁻¹
  set b := P⁻¹ - S⁻¹
  set c := Q⁻¹ - S⁻¹
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by linarith
  have hc : 0 ≤ c := by linarith
  have hgx : ∀ x, AEMeasurable (fun y => g (x - y)) :=
    fun x => hg.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
  -- Hölder à trois facteurs, à `x` fixé
  have point : ∀ x, ∫⁻ y, f y * g (x - y) ≤
      (∫⁻ y, f y ^ P * g (x - y) ^ Q) ^ a * A ^ b * B ^ c := by
    intro x
    have H := ENNReal.lintegral_prod_norm_pow_le (μ := volume) (Finset.univ : Finset (Fin 3))
      (f := ![fun y => f y ^ P * g (x - y) ^ Q, fun y => f y ^ P, fun y => g (x - y) ^ Q])
      (p := ![a, b, c]) ?_ ?_ ?_
    rotate_left
    · intro i _
      fin_cases i
      · exact (hf.pow_const P).mul ((hgx x).pow_const Q)
      · exact hf.pow_const P
      · exact (hgx x).pow_const Q
    · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      simp only [a, b, c]; linarith
    · intro i _
      fin_cases i <;> simp [ha, hb, hc]
    simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at H
    rw [lintegral_sub_left_eq_self (fun y => g y ^ Q) x] at H
    refine le_of_eq_of_le (lintegral_congr fun y => ?_) H
    have e1 : P * a + P * b = 1 := by simp only [a, b]; field_simp; ring
    have e2 : Q * a + Q * c = 1 := by simp only [a, c]; field_simp; ring
    rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
    calc f y * g (x - y) = f y ^ (P * a + P * b) * g (x - y) ^ (Q * a + Q * c) := by
          rw [e1, e2, ENNReal.rpow_one, ENNReal.rpow_one]
      _ = _ := by
          rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity),
            ENNReal.rpow_add_of_nonneg _ _ (by positivity) (by positivity)]
          ring
  have hK : AEMeasurable (fun x => ∫⁻ y, f y ^ P * g (x - y) ^ Q) :=
    (((hf.pow_const P).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      ((hg.pow_const Q).comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))).lintegral_prod_right'
  have aS : a * S = 1 := by simp only [a]; field_simp
  calc ∫⁻ x, (∫⁻ y, f y * g (x - y)) ^ S
      ≤ ∫⁻ x, (∫⁻ y, f y ^ P * g (x - y) ^ Q) * (A ^ (S * b) * B ^ (S * c)) := by
        refine lintegral_mono fun x => (ENNReal.rpow_le_rpow (point x) hS0.le).trans
          (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_nonneg _ _ hS0.le, ENNReal.mul_rpow_of_nonneg _ _ hS0.le,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, aS, ENNReal.rpow_one,
          mul_assoc, mul_comm b S, mul_comm c S]
    _ = (∫⁻ x, ∫⁻ y, f y ^ P * g (x - y) ^ Q) * (A ^ (S * b) * B ^ (S * c)) :=
        lintegral_mul_const'' _ hK
    _ = A ^ (S / P) * B ^ (S / Q) := by
        rw [lintegral_lintegral_mul_sub (hf.pow_const P) (hg.pow_const Q), ← hA, ← hB]
        have e1 : S / P = 1 + S * b := by simp only [b]; field_simp; ring
        have e2 : S / Q = 1 + S * c := by simp only [c]; field_simp; ring
        rw [e1, e2, ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity),
          ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by positivity), ENNReal.rpow_one,
          ENNReal.rpow_one]
        ring

/-- Inégalité de Young pour la convolution de fonctions positives :
si `p, q ≥ 1` et `1/p + 1/q = 1 + 1/r'`, alors `‖∫ f(y) g(· - y) dy‖_{r'} ≤ ‖f‖_p ‖g‖_q`. -/
theorem eLpNorm_lintegral_conv_le {p q r' : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : p⁻¹ + q⁻¹ = 1 + r'⁻¹) {f g : ℝᵈ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) :
    eLpNorm (fun x => ∫⁻ y, f y * g (x - y)) r' ≤ eLpNorm f p * eLpNorm g q := by
  have hpi : p⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hp
  have hqi : q⁻¹ ≤ 1 := ENNReal.inv_le_one.2 hq
  have hF : AEMeasurable (fun x => ∫⁻ y, f y * g (x - y)) :=
    ((hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
      (hg.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))).lintegral_prod_right'
  rcases eq_or_ne r' ∞ with rfl | hr
  · simp only [ENNReal.inv_top, add_zero] at hpqr
    have : p.HolderConjugate q := ENNReal.holderConjugate_iff.2 hpqr
    rw [eLpNorm_exponent_top hF.aestronglyMeasurable]
    refine eLpNormEssSup_le_of_ae_enorm_bound (ae_of_all _ fun x => ?_)
    rw [enorm_eq_self]
    refine (lintegral_mul_le_eLpNorm_mul_eLpNorm (p := p) (q := q) hf
      (hg.comp_quasiMeasurePreserving
      (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving)).trans
      (le_of_eq ?_)
    congr 1
    exact eLpNorm_comp_measurePreserving (g := g) hg.aestronglyMeasurable
      (Measure.measurePreserving_sub_left volume x)
  have key : ∀ s : ℝ≥0∞, s⁻¹ ≤ 1 → s⁻¹ = 1 + r'⁻¹ → False := by
    intro s hs h
    have h' : 1 + r'⁻¹ ≤ 1 + 0 := by rw [add_zero, ← h]; exact hs
    exact hr (ENNReal.inv_eq_zero.1
      (le_antisymm (ENNReal.le_of_add_le_add_left ENNReal.one_ne_top h') bot_le))
  have hp' : p ≠ ∞ := by
    rintro rfl
    exact key q hqi (by simpa using hpqr)
  have hq' : q ≠ ∞ := by
    rintro rfl
    exact key p hpi (by simpa using hpqr)
  have hr1 : 1 ≤ r' := by
    refine ENNReal.inv_le_one.1 (ENNReal.le_of_add_le_add_left ENNReal.one_ne_top ?_)
    rw [← hpqr]
    exact add_le_add hpi hqi
  have hr0 : r' ≠ 0 := (zero_lt_one.trans_le hr1).ne'
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr hF.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq' hg.aestronglyMeasurable]
  simp only [enorm_eq_self]
  set P := p.toReal with hP_def
  set Q := q.toReal with hQ_def
  set S := r'.toReal with hS_def
  have hP : 1 ≤ P := by simpa using ENNReal.toReal_mono hp' hp
  have hQ : 1 ≤ Q := by simpa using ENNReal.toReal_mono hq' hq
  have hS : 1 ≤ S := by simpa using ENNReal.toReal_mono hr hr1
  have hPQS : P⁻¹ + Q⁻¹ = 1 + S⁻¹ := by
    have := congrArg ENNReal.toReal hpqr
    rwa [ENNReal.toReal_add (by simpa using hp0) (by simpa using hq0),
      ENNReal.toReal_add ENNReal.one_ne_top (by simpa using hr0), ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_one] at this
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  refine (ENNReal.rpow_le_rpow (lintegral_conv_rpow_le hP hQ hS hPQS hf hg)
    (by positivity)).trans (le_of_eq ?_)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  congr 2 <;> field_simp

/-- Mesurabilité de `x ↦ ∫ f(y) g(x - y) dy` pour `f, g` positives. -/
theorem aemeasurable_lintegral_conv {f g : ℝᵈ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) : AEMeasurable (fun x => ∫⁻ y, f y * g (x - y)) :=
  ((hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
    (hg.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume))).lintegral_prod_right'

/-- **Th. `th:Young` (Inégalité de Young), forme trilinéaire.** Soient `p, q, r ∈ [1, ∞]`
tels que `1/p + 1/q + 1/r = 2`. Pour toutes fonctions mesurables positives `f, g, h` sur
`ℝ^d`, `I(f, g, h) := ∬ f(x) g(y - x) h(y) dy dx ≤ ‖f‖_p ‖g‖_q ‖h‖_r`.
(La preuve diffère de celle du cours : elle déduit cette forme de l'estimation de
convolution par l'inégalité de Hölder.) -/
theorem th_Young {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + q⁻¹ + r⁻¹ = 2) {f g h : ℝᵈ → ℝ≥0∞} (hf : AEMeasurable f)
    (hg : AEMeasurable g) (hh : AEMeasurable h) :
    ∫⁻ x, ∫⁻ y, f x * g (y - x) * h y ≤ eLpNorm f p * eLpNorm g q * eLpNorm h r := by
  have hsub : Measure.QuasiMeasurePreserving (fun z : ℝᵈ × ℝᵈ => z.2 - z.1)
      (volume.prod volume) volume :=
    (quasiMeasurePreserving_sub_of_right_invariant volume volume).comp
      Measure.measurePreserving_swap.quasiMeasurePreserving
  have hK : AEMeasurable (Function.uncurry fun x y => f x * g (y - x) * h y)
      (volume.prod volume) :=
    ((hf.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hg.comp_quasiMeasurePreserving hsub)).mul
      (hh.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  obtain ⟨r', hrr⟩ : ∃ r' : ℝ≥0∞, r'.HolderConjugate r :=
    ⟨_, (ENNReal.HolderConjugate.conjExponent hr).symm⟩
  have hpqr' : p⁻¹ + q⁻¹ = 1 + r'⁻¹ := by
    have h1 : r'⁻¹ + r⁻¹ = 1 := ENNReal.HolderConjugate.inv_add_inv_eq_one r' r
    have hri : r⁻¹ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (ENNReal.inv_le_one.2 hr)
    rw [← ENNReal.add_left_inj hri, hpqr, add_assoc, h1, one_add_one_eq_two]
  have hF := aemeasurable_lintegral_conv hf hg
  have e1 : ∫⁻ x, ∫⁻ y, f x * g (y - x) * h y = ∫⁻ y, (∫⁻ x, f x * g (y - x)) * h y := by
    rw [lintegral_lintegral_swap hK]
    refine lintegral_congr fun y => ?_
    exact lintegral_mul_const'' _ (hf.mul (hg.comp_quasiMeasurePreserving
          (Measure.measurePreserving_sub_left volume y).quasiMeasurePreserving))
  have e2 : ∫⁻ y, (∫⁻ x, f x * g (y - x)) * h y ≤
      eLpNorm (fun y => ∫⁻ x, f x * g (y - x)) r' * eLpNorm h r :=
    lintegral_mul_le_eLpNorm_mul_eLpNorm (p := r') (q := r) hF hh
  have e3 := eLpNorm_lintegral_conv_le hp hq hpqr' hf hg
  rw [e1]
  exact e2.trans (mul_le_mul_left e3 _)

/-- **Th. `th:Young` (Inégalité de Young), forme trilinéaire sur `L^p × L^q × L^r`.**
Soient `p, q, r ∈ [1, ∞]` tels que `1/p + 1/q + 1/r = 2`, et `f ∈ L^p(ℝ^d)`, `g ∈ L^q(ℝ^d)`,
`h ∈ L^r(ℝ^d)` réelles. Alors `(x, y) ↦ f(x) g(y - x) h(y)` est intégrable sur `ℝ^d × ℝ^d`
(donc `I(f, g, h)` est bien défini), et `|I(f, g, h)| ≤ ‖f‖_p ‖g‖_q ‖h‖_r`. -/
theorem th_Young_reel {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hpqr : p⁻¹ + q⁻¹ + r⁻¹ = 2) {f g h : ℝᵈ → ℝ} (hf : MemLp f p) (hg : MemLp g q)
    (hh : MemLp h r) :
    Integrable (fun z : ℝᵈ × ℝᵈ => f z.1 * g (z.2 - z.1) * h z.2) (volume.prod volume) ∧
      |∫ x, ∫ y, f x * g (y - x) * h y| ≤
        (eLpNorm f p * eLpNorm g q * eLpNorm h r).toReal := by
  have hm : AEStronglyMeasurable (fun z : ℝᵈ × ℝᵈ => f z.1 * g (z.2 - z.1) * h z.2)
      (volume.prod volume) :=
    ((hf.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving
        ((quasiMeasurePreserving_sub_of_right_invariant volume volume).comp
          Measure.measurePreserving_swap.quasiMeasurePreserving))).mul
      (hh.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have key : ∫⁻ z : ℝᵈ × ℝᵈ, ‖f z.1 * g (z.2 - z.1) * h z.2‖ₑ ∂(volume.prod volume) ≤
      eLpNorm f p * eLpNorm g q * eLpNorm h r := by
    rw [lintegral_prod _ hm.enorm]
    simp only [enorm_mul]
    have := th_Young hp hq hr hpqr hf.aestronglyMeasurable.enorm hg.aestronglyMeasurable.enorm
      hh.aestronglyMeasurable.enorm
    rwa [eLpNorm_enorm _ hf.aestronglyMeasurable, eLpNorm_enorm _ hg.aestronglyMeasurable,
      eLpNorm_enorm _ hh.aestronglyMeasurable] at this
  have hfin : eLpNorm f p * eLpNorm g q * eLpNorm h r ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top)
      hh.eLpNorm_ne_top
  have hint : Integrable (fun z : ℝᵈ × ℝᵈ => f z.1 * g (z.2 - z.1) * h z.2)
      (volume.prod volume) := ⟨hm, key.trans_lt hfin.lt_top⟩
  refine ⟨hint, ?_⟩
  rw [← integral_prod _ hint, ← Real.norm_eq_abs, ← toReal_enorm]
  exact ENNReal.toReal_mono hfin ((enorm_integral_le_lintegral_enorm _).trans key)

/-- **Th. `th:Young` (Inégalité de Young), estimation de convolution.** Soient
`p, q ∈ [1, ∞]` et `r'` tel que `1 + 1/r' = 1/p + 1/q`. Pour toutes `f ∈ L^p(ℝ^d)` et
`g ∈ L^q(ℝ^d)`, l'intégrale `(f ⋆ g)(x) = ∫ f(h) g(x - h) dh` converge pour presque tout `x`,
`f ⋆ g ∈ L^{r'}(ℝ^d)` et `‖f ⋆ g‖_{r'} ≤ ‖f‖_p ‖g‖_q`.
Remarque : la convolution est ici l'intégrale de Mathlib, définie presque partout ; le cours
l'obtient (pour `p, q < ∞`) comme prolongement continu de la convolution sur `C^0_c`, ce qui
donne la même fonction. La condition `r' ∈ [1, ∞]` découle de la relation entre exposants. -/
theorem th_Young_convol {p q r' : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpqr : 1 + r'⁻¹ = p⁻¹ + q⁻¹) {f g : ℝᵈ → ℝ} (hf : MemLp f p) (hg : MemLp g q) :
    (∀ᵐ x, ConvolutionExistsAt f g x (lsmul ℝ ℝ) volume) ∧ MemLp (f ⋆ g) r' ∧
      eLpNorm (f ⋆ g) r' ≤ eLpNorm f p * eLpNorm g q := by
  set F : ℝᵈ → ℝ≥0∞ := fun x => ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ with hF_def
  have hFm : AEMeasurable F :=
    aemeasurable_lintegral_conv hf.aestronglyMeasurable.enorm hg.aestronglyMeasurable.enorm
  have hFle : eLpNorm F r' ≤ eLpNorm f p * eLpNorm g q := by
    have := eLpNorm_lintegral_conv_le hp hq hpqr.symm hf.aestronglyMeasurable.enorm
      hg.aestronglyMeasurable.enorm
    rwa [eLpNorm_enorm _ hf.aestronglyMeasurable, eLpNorm_enorm _ hg.aestronglyMeasurable] at this
  have hfin : eLpNorm f p * eLpNorm g q < ∞ :=
    ENNReal.mul_lt_top hf.eLpNorm_lt_top hg.eLpNorm_lt_top
  have hfg : AEStronglyMeasurable (f ⋆ g) volume :=
    hf.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hg.aestronglyMeasurable
  have hle : eLpNorm (f ⋆ g) r' ≤ eLpNorm f p * eLpNorm g q :=
    (eLpNorm_mono_enorm hfg fun x => by
      rw [enorm_eq_self]; exact enorm_convolution_le_lintegral f g x).trans hFle
  have hmem : MemLp (f ⋆ g) r' := hle.trans_lt hfin
  refine ⟨?_, hmem, hle⟩
  have hr0 : r' ≠ 0 := by
    rintro rfl
    have h1 : p⁻¹ + q⁻¹ ≤ 1 + 1 :=
      add_le_add (ENNReal.inv_le_one.2 hp) (ENNReal.inv_le_one.2 hq)
    rw [← hpqr] at h1
    simp at h1
  have hae : ∀ᵐ x, F x < ∞ := by
    rcases eq_or_ne r' ∞ with rfl | hr
    · filter_upwards [ae_le_eLpNormEssSup (f := F) (μ := volume)] with x hx
      rw [enorm_eq_self, ← eLpNorm_exponent_top hFm.aestronglyMeasurable] at hx
      exact hx.trans_lt (hFle.trans_lt hfin)
    · have hS0 : 0 < r'.toReal := ENNReal.toReal_pos hr0 hr
      have h2 : ∫⁻ x, F x ^ r'.toReal ≠ ∞ := by
        have h3 := (hFle.trans_lt hfin)
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hr hFm.aestronglyMeasurable] at h3
        simp only [enorm_eq_self] at h3
        exact ((ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 h3).ne
      filter_upwards [ae_lt_top' (hFm.pow_const r'.toReal) h2] with x hx
      exact (ENNReal.rpow_lt_top_iff_of_pos hS0).1 hx
  filter_upwards [hae] with x hx
  exact convolutionExistsAt_of_lintegral_lt_top hf.aestronglyMeasurable hg.aestronglyMeasurable hx

end M1Analyse
