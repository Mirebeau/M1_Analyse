/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import M1Analyse.Dualite.DualiteLebesgue
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import M1Analyse.TopologieGenerale.EspacesFonctionnels
import M1Analyse.Bosse.Bosse
import M1Analyse.Outils.Schwarz

/-!
# §5.2 Convolution de distributions et espaces de Sobolev (`subsec:convolSobolev`)

Source : `Include/Sobolev.tex`, sous-section `subsec:convolSobolev` (début seulement).

La distribution `U_f` associée à `f ∈ L^1_loc(Ω)` est `Distribution.ofFun Ω f volume ⊤` de
Mathlib, de formule `⟨U_f, φ⟩ = ∫ φ f`. Les espaces de Sobolev `W^{s,p}(Ω)` (définis par
dérivées faibles) ne sont pas dans Mathlib (qui ne contient que les espaces de potentiel de
Bessel `H^{s,p}(ℝ^d)`, définis par transformée de Fourier) : la suite de la sous-section n'est
pas formalisée ici, à l'exception de `corol:distribLp` (`corol_distribLp`) et de
`prop:deriv_distrib` (`deriveeDistrib`) ; `W^{1,p}(Ω)` est dans `M1Analyse/Sobolev/W1p.lean`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal Distributions LineDeriv

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
Remarque : la continuité de `f ↦ U_f` (de `L^1_loc(Ω)` dans `𝓓'(Ω)`) n'est pas formalisée.
Preuve (différente du cours) : `Distribution.ofFun_injective` de Mathlib : des `φ_n ∈ C^∞_c`,
`= 1` sur un compact `K`, tendant vers `1_K`, donnent `∫_K f = 0` (convergence dominée), donc
`f = 0` p.p. ; au lieu de la régularisation `ρ_ε ⋆ f → f` du cours. -/
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
(Preuve, différente du cours : (a) ⇒ (b), `T` définit une forme linéaire continue sur
l'image de `𝓓(Ω)` dans `L^q(Ω)`, prolongée à `L^q(Ω)` par Hahn–Banach, puis représentée
par `f ∈ L^p` par `th:lpDualLq` (`th_lpDualLq_bijectif` si `p < ∞`,
`th_lpDualLq_bijectif_un` si `p = ∞`), au lieu du prolongement par densité de `𝓓(Ω)` dans
`L^q(Ω)` (`corol:testDenseLp`) ;
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

section DeriveeDistrib

/-- Les directions `e_i` (chacune répétée `α_i` fois) d'une dérivée partielle `∂_α`. -/
noncomputable def dirMulti (α : Fin d → ℕ) : Fin (directions α).length → ℝᵈ :=
  fun j => EuclideanSpace.single ((directions α).get j) (1 : ℝ)

/-- **Prop. `prop:deriv_distrib` (Dérivation d'une distribution), définition.** Pour
`T ∈ 𝓓'(Ω)` et `α ∈ ℕ^d`, `∂_α T` est la dérivée itérée de Mathlib `∂^{…} T` dans les directions
`e_i`, chacune répétée `α_i` fois ; elle vérifie `⟨∂_α T, φ⟩ = (-1)^s ⟨T, ∂_α φ⟩`, `s = |α|₁`
(`prop_deriv_distrib_apply`). -/
noncomputable def deriveeDistrib (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    (T : 𝓓'(Ω, ℝ)) : 𝓓'(Ω, ℝ) :=
  ∂^{dirMulti α} T

private lemma derivDistrib_coe_lineDeriv (Ω : TopologicalSpace.Opens ℝᵈ) (v : ℝᵈ)
    (φ : 𝓓(Ω, ℝ)) (x : ℝᵈ) : (∂_{v} φ : 𝓓(Ω, ℝ)) x = fderiv ℝ φ x v := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]

private lemma derivDistrib_coe_iter (Ω : TopologicalSpace.Opens ℝᵈ) {n : ℕ} (v : Fin n → ℝᵈ)
    (φ : 𝓓(Ω, ℝ)) (x : ℝᵈ) :
    (∂^{v} φ : 𝓓(Ω, ℝ)) x = iteratedFDeriv ℝ n φ x v := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, derivDistrib_coe_lineDeriv,
      iteratedFDeriv_succ_apply_left]
    have : (⇑(∂^{Fin.tail v} φ : 𝓓(Ω, ℝ))) = fun y => iteratedFDeriv ℝ n φ y (Fin.tail v) :=
      funext (ih _)
    rw [this, fderiv_continuousMultilinear_apply_const_apply]
    exact (φ.contDiff.differentiable_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top n)).differentiableAt

/-- Pont : la dérivée itérée de Mathlib d'une fonction test, dans les directions de `α`, est
la dérivée partielle `∂_α φ` du cours (`deriveePartielle`). -/
theorem coe_iteratedLineDeriv_testFunction (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    (φ : 𝓓(Ω, ℝ)) : ((∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) : ℝᵈ → ℝ) = deriveePartielle α φ :=
  funext fun x => derivDistrib_coe_iter Ω _ φ x

/-- Lemme de Schwarz pour les fonctions test : l'ordre des dérivations est indifférent. -/
private lemma derivDistrib_iter_perm (Ω : TopologicalSpace.Opens ℝᵈ) {n : ℕ} (v : Fin n → ℝᵈ)
    (σ : Equiv.Perm (Fin n)) (φ : 𝓓(Ω, ℝ)) : (∂^{v ∘ σ} φ : 𝓓(Ω, ℝ)) = ∂^{v} φ := by
  ext x
  rw [derivDistrib_coe_iter, derivDistrib_coe_iter]
  exact iteratedFDeriv_comp_perm_of_contDiff n (φ.contDiff.of_le (by exact_mod_cast le_top)) x v σ

private lemma derivDistrib_init_rev {α : Type*} {n : ℕ} (v : Fin (n + 1) → α) :
    Fin.init (v ∘ Fin.rev) = Fin.tail v ∘ Fin.rev := by
  funext i
  simp only [Fin.init, Fin.tail, Function.comp_apply]
  congr 1
  ext
  simp [Fin.val_rev]
  omega

private lemma derivDistrib_apply_rev (Ω : TopologicalSpace.Opens ℝᵈ) {n : ℕ} (v : Fin n → ℝᵈ)
    (T : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ)) : (∂^{v} T) φ = (-1) ^ n * T (∂^{v ∘ Fin.rev} φ) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, Distribution.lineDerivOp_apply_apply, map_neg,
      ih, LineDeriv.iteratedLineDerivOp_succ_right (v ∘ Fin.rev), derivDistrib_init_rev]
    simp [pow_succ]

/-- **Prop. `prop:deriv_distrib`, formule.** `⟨∂_α T, φ⟩ = (-1)^s ⟨T, ∂_α φ⟩`, avec `s = |α|₁` ;
en particulier `∂_α T ∈ 𝓓'(Ω)`. -/
theorem prop_deriv_distrib_apply (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    (T : 𝓓'(Ω, ℝ)) (φ : 𝓓(Ω, ℝ)) :
    deriveeDistrib Ω α T φ = (-1) ^ (∑ i, α i) * T (∂^{dirMulti α} φ) := by
  rw [deriveeDistrib, derivDistrib_apply_rev, ← length_directions]
  exact congrArg _ (congrArg T (derivDistrib_iter_perm Ω (dirMulti α) Fin.revPerm φ))

/-- **Prop. `prop:deriv_distrib`, continuité** de `∂_α : 𝓓'(Ω) → 𝓓'(Ω)` pour la topologie de
Mathlib sur `𝓓'(Ω)` (convergence uniforme sur les bornés de `𝓓(Ω)`). -/
theorem prop_deriv_distrib_continuous (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ) :
    Continuous (deriveeDistrib Ω α) :=
  LineDeriv.continuous_iteratedLineDerivOp _

/-- **Prop. `prop:deriv_distrib`, continuité au sens des distributions** (convergence simple,
topologie faible-*) : si `T_i → T₀` au sens des distributions, alors `∂_α T_i → ∂_α T₀`. -/
theorem prop_deriv_distrib_tendsto (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    {ι : Type*} {l : Filter ι} {T : ι → 𝓓'(Ω, ℝ)} {T₀ : 𝓓'(Ω, ℝ)}
    (hT : ∀ φ : 𝓓(Ω, ℝ), Tendsto (fun i => T i φ) l (𝓝 (T₀ φ))) (φ : 𝓓(Ω, ℝ)) :
    Tendsto (fun i => deriveeDistrib Ω α (T i) φ) l (𝓝 (deriveeDistrib Ω α T₀ φ)) := by
  simp only [prop_deriv_distrib_apply]
  exact (hT _).const_mul _

private lemma derivDistrib_iter_append {V E : Type*} [LineDeriv V E E] {m n : ℕ}
    (u : Fin m → V) (v : Fin n → V) (f : E) : ∂^{u} (∂^{v} f) = ∂^{Fin.append u v} f := by
  induction n generalizing f with
  | zero =>
    rw [Fin.append_right_nil u v rfl, LineDeriv.iteratedLineDerivOp_fin_zero]
    rfl
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_right v, ih,
      LineDeriv.iteratedLineDerivOp_succ_right (Fin.append (m := m) (n := n + 1) u v)]
    have h := Fin.append_snoc u (Fin.init v) (v (Fin.last n))
    rw [Fin.snoc_init_self] at h
    rw [h, Fin.init_snoc, Fin.snoc_last]

private lemma derivDistrib_tsupport (Ω : TopologicalSpace.Opens ℝᵈ) {n : ℕ} (v : Fin n → ℝᵈ)
    (φ : 𝓓(Ω, ℝ)) : tsupport (∂^{v} φ : 𝓓(Ω, ℝ)) ⊆ tsupport φ := by
  have : (⇑(∂^{v} φ : 𝓓(Ω, ℝ))) = (fun M => M v) ∘ iteratedFDeriv ℝ n φ :=
    funext (derivDistrib_coe_iter Ω v φ)
  rw [this]
  exact (tsupport_comp_subset (by simp) _).trans (tsupport_iteratedFDeriv_subset n)

private lemma derivDistrib_bdd (Ω : TopologicalSpace.Opens ℝᵈ) (φ : 𝓓(Ω, ℝ)) (N : ℕ) :
    ∃ c : ℝ, ∀ x : ℝᵈ, ∀ α : Fin d → ℕ, ∑ i, α i ≤ N → ‖deriveePartielle α φ x‖ ≤ c := by
  have hb : ∀ j : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ C := fun j =>
    (φ.contDiff.continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (φ.hasCompactSupport.iteratedFDeriv j)
  choose C hC using hb
  refine ⟨∑ j ∈ Finset.range (N + 1), max (C j) 0, fun x α hα => ?_⟩
  have hj : (directions α).length ∈ Finset.range (N + 1) := by
    rw [Finset.mem_range, length_directions]; omega
  calc ‖deriveePartielle α φ x‖ ≤ ‖iteratedFDeriv ℝ (directions α).length φ x‖ :=
        norm_deriveePartielle_le α φ x
    _ ≤ max (C (directions α).length) 0 := (hC _ x).trans (le_max_left _ _)
    _ ≤ _ := Finset.single_le_sum (f := fun j => max (C j) 0) (fun _ _ => le_max_right _ _) hj

/-- **Prop. `prop:deriv_distrib`, ordre.** Si `T` vérifie l'estimation `eq:distrib_cont_loc`
d'ordre `n` sur le compact `K ⊂ Ω`, alors `∂_α T` la vérifie à l'ordre `n + s`, `s = |α|₁` :
`n_K(∂_α T) ≤ n_K(T) + s`, donc `ordre(∂_α T) ≤ ordre(T) + s`. -/
theorem prop_deriv_distrib_ordre (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    (T : 𝓓'(Ω, ℝ)) {K : Set ℝᵈ} (_hK : IsCompact K) (_hKΩ : K ⊆ Ω) {n : ℕ}
    (hT : ∃ C : ℝ, ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K → |T φ| ≤ C * normeK K n φ) :
    ∃ C : ℝ, ∀ φ : 𝓓(Ω, ℝ), tsupport φ ⊆ K →
      |deriveeDistrib Ω α T φ| ≤ C * normeK K (n + ∑ i, α i) φ := by
  obtain ⟨C, hC⟩ := hT
  refine ⟨max C 0, fun φ hφ => ?_⟩
  rw [prop_deriv_distrib_apply, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  obtain ⟨c, hc⟩ := derivDistrib_bdd Ω φ (n + ∑ i, α i)
  have key : normeK K n (∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) ≤ normeK K (n + ∑ i, α i) φ := by
    refine normeK_le (normeK_nonneg _ _ _) fun x hx β hβ => ?_
    have hw : Fin.append (dirMulti β) (dirMulti α) = fun k => EuclideanSpace.single
        (Fin.append (directions β).get (directions α).get k) (1 : ℝ) := by
      funext k
      refine Fin.addCases (fun i => ?_) (fun i => ?_) k <;> simp [dirMulti]
    rw [← congrFun (coe_iteratedLineDeriv_testFunction Ω β _) x, derivDistrib_iter_append,
      derivDistrib_coe_iter, hw, iteratedFDeriv_eq_deriveePartielle_multiIndice
        (φ.contDiff.of_le (by exact_mod_cast le_top))]
    refine le_normeK (fun y _ γ hγ => hc y γ hγ) hx ?_
    rw [sum_multiIndice, length_directions, length_directions]
    omega
  calc |T (∂^{dirMulti α} φ)| ≤ C * normeK K n (∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) :=
        hC _ ((derivDistrib_tsupport Ω _ φ).trans hφ)
    _ ≤ max C 0 * normeK K n (∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) := by
        gcongr
        · exact normeK_nonneg _ _ _
        · exact le_max_left _ _
    _ ≤ max C 0 * normeK K (n + ∑ i, α i) φ := by
        gcongr

private lemma derivDistrib_snoc_rev {α : Type*} {n : ℕ} (v : Fin (n + 1) → α) :
    Fin.snoc (Fin.tail v ∘ Fin.rev) (v 0) = v ∘ Fin.rev := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · simp only [Fin.snoc_castSucc, Fin.tail, Function.comp_apply]
    congr 1
    ext
    simp [Fin.val_rev]
    omega

/-- Dérivée itérée de `x ↦ Dg(x) w`. -/
private lemma derivDistrib_iteratedFDeriv_fderiv_apply {n : ℕ} {g : ℝᵈ → ℝ}
    (hg : ContDiff ℝ (n + 1 : ℕ) g) (w : ℝᵈ) (x : ℝᵈ) (u : Fin n → ℝᵈ) :
    iteratedFDeriv ℝ n (fun y => fderiv ℝ g y w) x u =
      iteratedFDeriv ℝ (n + 1) g x (Fin.snoc u w) := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have h : (fun y => fderiv ℝ g y w) = ContinuousLinearMap.apply ℝ ℝ w ∘ fderiv ℝ g := rfl
  rw [h, ContinuousLinearMap.iteratedFDeriv_comp_left _
    ((hg.fderiv_right (m := n) (by push_cast; exact le_rfl)).contDiffAt) le_rfl]
  rfl

/-- Intégrations par parties itérées contre une fonction test. -/
private lemma derivDistrib_ibp (Ω : TopologicalSpace.Opens ℝᵈ) (φ : 𝓓(Ω, ℝ)) :
    ∀ (n : ℕ) (g : ℝᵈ → ℝ), ContDiff ℝ n g → ∀ v : Fin n → ℝᵈ,
      ∫ x, (∂^{v} φ : 𝓓(Ω, ℝ)) x * g x =
        (-1) ^ n * ∫ x, φ x * iteratedFDeriv ℝ n g x (v ∘ Fin.rev) := by
  intro n
  induction n with
  | zero => intro g _ v; simp
  | succ n ih =>
    intro g hg v
    set ψ : 𝓓(Ω, ℝ) := ∂^{Fin.tail v} φ with hψ
    have hg1 : Differentiable ℝ g := hg.differentiable (by simp)
    have hgc : Continuous fun x => fderiv ℝ g x (v 0) :=
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψd : Differentiable ℝ ψ := ψ.contDiff.differentiable (by simp)
    have hψ' : ∀ x, fderiv ℝ ψ x (v 0) = (∂_{v 0} ψ : 𝓓(Ω, ℝ)) x :=
      fun x => (derivDistrib_coe_lineDeriv Ω (v 0) ψ x).symm
    have H := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v 0)
      (f := ψ) (g := g)
      (by
        simp_rw [hψ']
        exact ((∂_{v 0} ψ : 𝓓(Ω, ℝ)).continuous.mul hg.continuous).integrable_of_hasCompactSupport
          (∂_{v 0} ψ : 𝓓(Ω, ℝ)).hasCompactSupport.mul_right)
      ((ψ.continuous.mul hgc).integrable_of_hasCompactSupport ψ.hasCompactSupport.mul_right)
      ((ψ.continuous.mul hg.continuous).integrable_of_hasCompactSupport
        ψ.hasCompactSupport.mul_right)
      (fun x _ => hψd x) (fun x _ => hg1 x)
    rw [LineDeriv.iteratedLineDerivOp_succ_left, ← hψ]
    simp_rw [← hψ']
    have hh : ContDiff ℝ n fun y => fderiv ℝ g y (v 0) :=
      (hg.fderiv_right (m := n) (by push_cast; exact le_rfl)).clm_apply contDiff_const
    have H2 := ih _ hh (Fin.tail v)
    rw [← hψ] at H2
    simp_rw [derivDistrib_iteratedFDeriv_fderiv_apply hg, derivDistrib_snoc_rev] at H2
    rw [eq_neg_iff_add_eq_zero, add_comm, ← eq_neg_iff_add_eq_zero] at H
    rw [H, H2, pow_succ]
    ring

/-- **Prop. `prop:deriv_distrib`, distributions fonctions.** Pour `f ∈ C^s(Ω)` (`s = |α|₁`),
`∂_α U_f = U_{∂_α f}`.
Preuve : intégrations par parties itérées, après multiplication de `f` par une fonction plateau
égale à `1` au voisinage du support de la fonction test (`prop:cinfSupport`). -/
theorem prop_deriv_distrib_ofFun (Ω : TopologicalSpace.Opens ℝᵈ) (α : Fin d → ℕ)
    {f : ℝᵈ → ℝ} (hf : ContDiffOn ℝ (∑ i, α i : ℕ) f Ω) :
    deriveeDistrib Ω α (Distribution.ofFun Ω f volume ⊤) =
      Distribution.ofFun Ω (deriveePartielle α f) volume ⊤ := by
  have hΩ : IsOpen (Ω : Set ℝᵈ) := Ω.isOpen
  rw [← length_directions] at hf
  set n := (directions α).length
  have hloc : LocallyIntegrableOn f Ω volume :=
    hf.continuousOn.locallyIntegrableOn hΩ.measurableSet
  have hloc' : LocallyIntegrableOn (deriveePartielle α f) Ω volume := by
    refine ContinuousOn.locallyIntegrableOn ?_ hΩ.measurableSet
    refine ContinuousOn.congr (f := fun x => iteratedFDerivWithin ℝ n f Ω x (dirMulti α)) ?_
      fun x hx => deriveePartielle_eq_iteratedFDerivWithin hΩ α f hx
    exact (ContinuousMultilinearMap.apply ℝ (fun _ => ℝᵈ) ℝ
      (dirMulti α)).continuous.comp_continuousOn
      (hf.continuousOn_iteratedFDerivWithin le_rfl hΩ.uniqueDiffOn)
  ext φ
  rw [prop_deriv_distrib_apply, Distribution.ofFun_apply hloc, Distribution.ofFun_apply hloc',
    ← length_directions]
  simp only [smul_eq_mul]
  -- fonction plateau `χ`, égale à `1` sur un voisinage ouvert `U` de `supp φ`
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure
    φ.hasCompactSupport.isCompact hΩ φ.tsupport_subset
  obtain ⟨χ, hχ, -, hχΩ, -, hχ1⟩ := prop_cinfSupport hΩ hUc hUΩ
  set g : ℝᵈ → ℝ := fun x => χ x * f x
  have hg : ContDiff ℝ n g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ (Ω : Set ℝᵈ)
    · exact (hχ.contDiffAt.of_le (by exact_mod_cast le_top)).mul
        (hf.contDiffAt (hΩ.mem_nhds hx))
    · have h0 : g =ᶠ[𝓝 x] fun _ => 0 := by
        have := (notMem_tsupport_iff_eventuallyEq.1 fun h => hx (hχΩ h))
        filter_upwards [this] with y hy
        simp [g, hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  have hgU : ∀ x ∈ U, g x = f x := fun x hx => by
    simp [g, hχ1 (subset_closure hx)]
  have h1 : ∫ x, (∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) x * f x =
      ∫ x, (∂^{dirMulti α} φ : 𝓓(Ω, ℝ)) x * g x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · simp [hgU x hx]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hKU (derivDistrib_tsupport Ω _ φ h))]
  have h2 : ∫ x, φ x * iteratedFDeriv ℝ n g x (dirMulti α ∘ Fin.rev) =
      ∫ x, φ x * deriveePartielle α f x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ U
    · have hs : iteratedFDeriv ℝ n g x (dirMulti α ∘ Fin.rev) =
          iteratedFDeriv ℝ n g x (dirMulti α) :=
        iteratedFDeriv_comp_perm_of_contDiff n hg x (dirMulti α) Fin.revPerm
      have he : iteratedFDeriv ℝ n g x = iteratedFDeriv ℝ n f x :=
        (Filter.EventuallyEq.iteratedFDeriv ℝ
          (Filter.eventually_of_mem (hUo.mem_nhds hx) hgU) n).eq_of_nhds
      change _ * _ = _ * _
      rw [hs, he]
      rfl
    · simp [image_eq_zero_of_notMem_tsupport fun h => hx (hKU h)]
  rw [h1, derivDistrib_ibp Ω φ n g hg, h2, ← mul_assoc]
  change (-1) ^ n * (-1) ^ n * _ = _
  rw [← mul_pow]
  simp

end DeriveeDistrib

end M1Analyse
