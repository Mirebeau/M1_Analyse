/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import M1Analyse.Dualite.DualiteLebesgue

/-!
# §5.2 Convolution de distributions et espaces de Sobolev (`subsec:convolSobolev`)

Source : `Include/Sobolev.tex`, sous-section `subsec:convolSobolev` (début seulement).

La distribution `U_f` associée à `f ∈ L^1_loc(Ω)` est `Distribution.ofFun Ω f volume ⊤` de
Mathlib, de formule `⟨U_f, φ⟩ = ∫ φ f`. Les espaces de Sobolev `W^{s,p}(Ω)` (définis par
dérivées faibles) ne sont pas dans Mathlib (qui ne contient que les espaces de potentiel de
Bessel `H^{s,p}(ℝ^d)`, définis par transformée de Fourier) : la suite de la sous-section n'est
pas formalisée, à l'exception de `corol:distribLp` (`corol_distribLp`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Distributions

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Prop. `prop:distribL1Loc` (Distribution associée à une fonction), définition.**
Pour `f ∈ L^1_loc(Ω)` et `φ ∈ 𝓓(Ω)`, `⟨U_f, φ⟩ = ∫_Ω f φ`, où `U_f` est la distribution
Mathlib `Distribution.ofFun Ω f volume ⊤` (l'intégrale peut être prise sur `ℝ^d`, `φ` étant
nulle hors de `Ω`). -/
theorem prop_distribL1Loc_apply (Ω : TopologicalSpace.Opens ℝᵈ) {f : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) (φ : 𝓓(Ω, ℝ)) :
    Distribution.ofFun Ω f volume ⊤ φ = ∫ x, f x * φ x := by
  rw [Distribution.ofFun_apply hf]
  simp only [smul_eq_mul, mul_comm]

/-- **Prop. `prop:distribL1Loc`, ordre `0`.** Pour `K ⊂⊂ Ω` compact et `φ ∈ 𝓓_K(Ω)` avec
`|φ| ≤ C`, on a `|⟨U_f, φ⟩| ≤ C ‖f‖_{L^1(K)}` : `U_f` est d'ordre `0`. -/
theorem prop_distribL1Loc_ordre (Ω : TopologicalSpace.Opens ℝᵈ) {f : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) {K : Set ℝᵈ} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (φ : 𝓓(Ω, ℝ)) (hφK : tsupport φ ⊆ K) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) :
    |Distribution.ofFun Ω f volume ⊤ φ| ≤ C * ∫ x in K, |f x| := by
  have hfK : IntegrableOn f K := hf.integrableOn_compact_subset hKΩ hK
  rw [prop_distribL1Loc_apply Ω hf φ, ← integral_const_mul,
    ← integral_indicator hK.measurableSet, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (IntegrableOn.integrable_indicator
    (hfK.norm.const_mul C) hK.measurableSet) (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ K
  · rw [indicator_of_mem hx, norm_mul, mul_comm, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
  · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hφK h)
    simp [indicator_of_notMem hx, this]

/-- **Prop. `prop:distribL1Loc`, injectivité.** Si `f, g ∈ L^1_loc(Ω)` vérifient `U_f = U_g`,
alors `f = g` presque partout sur `Ω`.
Remarque : la continuité de `f ↦ U_f` (de `L^1_loc(Ω)` dans `𝓓'(Ω)`) n'est pas formalisée. -/
theorem prop_distribL1Loc_injective (Ω : TopologicalSpace.Opens ℝᵈ) {f g : ℝᵈ → ℝ}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω)
    (h : Distribution.ofFun Ω f volume ⊤ = Distribution.ofFun Ω g volume ⊤) :
    f =ᵐ[volume.restrict (Ω : Set ℝᵈ)] g :=
  Distribution.ofFun_injective hf hg h

section DistribLp

/-- Une fonction test est dans `L^q(Ω)` pour tout `q`. -/
private lemma distribLp_memLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) (φ : 𝓓(Ω, ℝ)) :
    MemLp φ q (volume.restrict (Ω : Set ℝᵈ)) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- `∫_Ω φ g = ∫_{ℝ^d} g φ`, `φ` étant nulle hors de `Ω`. -/
private lemma distribLp_integral (Ω : TopologicalSpace.Opens ℝᵈ) (g : ℝᵈ → ℝ)
    (φ : 𝓓(Ω, ℝ)) : ∫ x in (Ω : Set ℝᵈ), φ x * g x = ∫ x, g x * φ x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp_rw [mul_comm]
  · intro x hx
    simp [φ.zero_on_compl hx]

/-- `L^p(Ω) ⊆ L^1_loc(Ω)` pour `p ≥ 1`. -/
private lemma distribLp_locInt (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {f : ℝᵈ → ℝ} (hf : MemLp f p (volume.restrict (Ω : Set ℝᵈ))) :
    LocallyIntegrableOn f Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)

/-- L'injection linéaire `𝓓(Ω) → L^q(Ω)`. -/
private noncomputable def distribLp_toLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) :
    𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) where
  toFun φ := (distribLp_memLp Ω q φ).toLp φ
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    rfl

private lemma distribLp_norm_toLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (φ : 𝓓(Ω, ℝ)) :
    ‖distribLp_toLp Ω q φ‖ = (eLpNorm φ q (volume.restrict (Ω : Set ℝᵈ))).toReal :=
  Lp.norm_toLp _ (distribLp_memLp Ω q φ)

/-- **Cor. `corol:distribLp`.** Soient `T ∈ 𝓓'(Ω)`, `p ∈ ]1, ∞]` et `q` l'exposant conjugué
(`1/p + 1/q = 1`). Les assertions suivantes sont équivalentes :
(a) il existe `C` tel que `|T(φ)| ≤ C ‖φ‖_{L^q(Ω)}` pour toute `φ ∈ 𝓓(Ω)` ;
(b) il existe `f ∈ L^p(Ω)` telle que `T = U_f`.
Ici `U_f` est la distribution `Distribution.ofFun Ω f volume ⊤` de Mathlib, `⟨U_f, φ⟩ = ∫ f φ`
(`prop_distribL1Loc_apply`), et `L^r(Ω)` est pris pour la mesure de Lebesgue restreinte à `Ω`.
(Preuve : (a) ⇒ (b), `T` définit une forme linéaire continue sur l'image de `𝓓(Ω)` dans
`L^q(Ω)`, prolongée à `L^q(Ω)` par Hahn–Banach, puis représentée par `f ∈ L^p` par
`th:lpDualLq` (`th_lpDualLq_bijectif` si `p < ∞`, `th_lpDualLq_bijectif_un` si `p = ∞`) ;
(b) ⇒ (a), inégalité de Hölder avec `C = ‖f‖_p`.) -/
theorem corol_distribLp (Ω : TopologicalSpace.Opens ℝᵈ) (T : 𝓓'(Ω, ℝ)) {p q : ℝ≥0∞}
    (hp : 1 < p) (hpq : p⁻¹ + q⁻¹ = 1) :
    (∃ C : ℝ, ∀ φ : 𝓓(Ω, ℝ), |T φ| ≤ C * (eLpNorm φ q (volume.restrict (Ω : Set ℝᵈ))).toReal) ↔
      ∃ f : ℝᵈ → ℝ, MemLp f p (volume.restrict (Ω : Set ℝᵈ)) ∧
        T = Distribution.ofFun Ω f volume ⊤ := by
  set μ := volume.restrict (Ω : Set ℝᵈ) with hμ
  have hq1 : 1 ≤ q := by
    rw [← ENNReal.inv_le_one, ← hpq]
    exact le_add_self
  constructor
  · rintro ⟨C, hC⟩
    have : Fact (1 ≤ p) := ⟨hp.le⟩
    have : Fact (1 ≤ q) := ⟨hq1⟩
    have : p.HolderConjugate q := ⟨by rw [hpq, inv_one]⟩
    set ι := distribLp_toLp Ω q
    have hC' : ∀ φ, |T φ| ≤ C * ‖ι φ‖ := fun φ => by
      rw [distribLp_norm_toLp]; exact hC φ
    have hker : LinearMap.ker ι ≤ LinearMap.ker (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) := by
      intro φ hφ
      rw [LinearMap.mem_ker] at hφ ⊢
      have := hC' φ
      rw [hφ, norm_zero, mul_zero] at this
      exact abs_nonpos_iff.1 this
    let S₀ : LinearMap.range ι →ₗ[ℝ] ℝ :=
      ((LinearMap.ker ι).liftQ (T : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) hker).comp
        (ι.quotKerEquivRange.symm : LinearMap.range ι →ₗ[ℝ] _)
    have hS₀ : ∀ φ, S₀ ⟨ι φ, LinearMap.mem_range_self ι φ⟩ = T φ := fun φ => by
      simp [S₀]
    let S : StrongDual ℝ (LinearMap.range ι) := S₀.mkContinuous C fun x => by
      obtain ⟨_, φ, rfl⟩ := x
      rw [hS₀, Real.norm_eq_abs]
      exact hC' φ
    obtain ⟨L, hL, -⟩ := exists_extension_norm_eq (LinearMap.range ι) S
    have hsurj : Function.Surjective (dualLp μ q p) := by
      by_cases hpt : p = ∞
      · subst hpt
        have : q = 1 := by simpa using hpq
        subst this
        exact th_lpDualLq_bijectif_un.2
      · have hq : 1 < q := by
          refine lt_of_le_of_ne hq1 fun h => hpt ?_
          subst h
          simpa using hpq
        have hqt : q ≠ ∞ := by
          rintro rfl
          exact hp.ne' (by simpa using hpq)
        exact (th_lpDualLq_bijectif hq hqt).2
    obtain ⟨g, hg⟩ := hsurj L
    refine ⟨g, Lp.memLp g, ?_⟩
    ext φ
    rw [prop_distribL1Loc_apply Ω (distribLp_locInt Ω hp.le (Lp.memLp g)), ← hS₀,
      ← distribLp_integral]
    calc S₀ ⟨ι φ, _⟩ = S ⟨ι φ, LinearMap.mem_range_self ι φ⟩ := rfl
      _ = L (ι φ) := (hL _).symm
      _ = dualLp μ q p g (ι φ) := by rw [hg]
      _ = ∫ x, ι φ x * g x ∂μ := dualLp_apply _ _
      _ = _ := integral_congr_ae (by
        filter_upwards [MemLp.coeFn_toLp (distribLp_memLp Ω q φ)] with x hx
        change (distribLp_memLp Ω q φ).toLp φ x * g x = φ x * g x
        rw [hx])
  · rintro ⟨f, hf, rfl⟩
    refine ⟨(eLpNorm f p μ).toReal, fun φ => ?_⟩
    have hφ := distribLp_memLp Ω q φ
    rw [prop_distribL1Loc_apply Ω (distribLp_locInt Ω hp.le hf), ← distribLp_integral, abs_le]
    constructor
    · have h := (th_HolderIneq hpq hf.neg hφ).2
      rw [eLpNorm_neg] at h
      simp only [Pi.neg_apply, neg_mul, integral_neg] at h
      simp_rw [mul_comm (φ _)]
      linarith
    · simp_rw [mul_comm (φ _)]
      exact (th_HolderIneq hpq hf hφ).2

end DistribLp

end M1Analyse
