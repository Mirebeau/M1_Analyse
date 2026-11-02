/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Sobolev.ConvolutionSobolev
import M1Analyse.Sobolev.ConvolutionLp

/-!
# Convolution d'une distribution et d'une fonction test (`def:convolDistrib`)

`(T ⋆ ρ)(x) := ⟨T, ρ(x - ·)⟩` pour `T ∈ 𝓓'(ℝ^d)` et `ρ ∈ 𝓓(ℝ^d)` (`convolDistrib`), et
`prop:convolDistrib` : identité `⟨T ⋆ ρ, φ⟩ = ⟨T, ρ̄ ⋆ φ⟩`, (i) `T ⋆ ρ ∈ C^∞`, (ii) dérivées,
(iii) `T ⋆ ρ_ε ⇀ (∫ ρ) T` et densité de `C^∞` dans `𝓓'`. Ainsi que `corol:convolTestFun` dans le
cas `Ω = ℝ^d`, utilisé pour (iii).

Preuve (différente du cours) : route directe. Le cours définit `T * ρ` par `⟨T, ρ̄ ⋆ φ⟩`, montre
qu'il est dans `L^∞_loc` ainsi que ses dérivées, en déduit `C^∞`, puis l'identifie à `T ⋆ ρ`. Ici
on dérive directement `x ↦ ⟨T, ρ(x - ·)⟩` (continuité de `T` sur `𝓓_K`), et l'identité s'obtient
par Hahn–Banach et intégrale de Bochner (Mathlib n'a pas d'intégrale à valeurs dans `𝓓_K`).
-/

open Set Filter Topology MeasureTheory TopologicalSpace
open scoped ContDiff Convolution Distributions LineDeriv
open ContinuousLinearMap (lsmul)

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "𝓓ᵈ" => 𝓓((⊤ : Opens (EuclideanSpace ℝ (Fin d))), ℝ)
local notation "𝓓'ᵈ" => 𝓓'((⊤ : Opens (EuclideanSpace ℝ (Fin d))), ℝ)

/-- La fonction test `y ↦ ρ(x - y)`. -/
noncomputable def translRefl (ρ : 𝓓ᵈ) (x : ℝᵈ) : 𝓓ᵈ where
  toFun y := ρ (x - y)
  contDiff' := ρ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := by simp

@[simp] lemma translRefl_apply (ρ : 𝓓ᵈ) (x y : ℝᵈ) : translRefl ρ x y = ρ (x - y) := rfl

/-- `ρ̄(y) := ρ(-y)` (notation `\overline ρ` du cours). -/
noncomputable def reflTest (ρ : 𝓓ᵈ) : 𝓓ᵈ where
  toFun y := ρ (-y)
  contDiff' := ρ.contDiff.comp contDiff_neg
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.neg _)
  tsupport_subset' := by simp

/-- Convolée `ψ ⋆ φ` de deux fonctions test, comme fonction test. -/
noncomputable def convolTest (ψ φ : 𝓓ᵈ) : 𝓓ᵈ where
  toFun := ψ ⋆[lsmul ℝ ℝ] φ
  contDiff' := φ.hasCompactSupport.contDiff_convolution_right (lsmul ℝ ℝ)
    ψ.continuous.locallyIntegrable φ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport.convolution (lsmul ℝ ℝ) φ.hasCompactSupport
  tsupport_subset' := by simp

/-- **Déf. `def:convolDistrib` (Convolution d'une distribution).** Pour `T ∈ 𝓓'(ℝ^d)` et
`ρ ∈ 𝓓(ℝ^d)`, `(T ⋆ ρ)(x) := ⟨T, ρ(x - ·)⟩`. -/
noncomputable def convolDistrib (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) : ℝᵈ → ℝ :=
  fun x => T (translRefl ρ x)

/-- Le noyau `ρ_ε = ε^{-d} ρ(·/ε)` (`noyauEps`), comme fonction test. -/
noncomputable def noyauEpsTest (ρ : 𝓓ᵈ) (ε : ℝ) : 𝓓ᵈ where
  toFun := noyauEps ρ ε
  contDiff' := contDiff_const.mul (ρ.contDiff.comp (contDiff_id.const_smul ε⁻¹))
  hasCompactSupport' := by
    by_cases hε : ε = 0
    · subst hε
      rcases Nat.eq_zero_or_pos d with hd | hd
      · subst hd; exact HasCompactSupport.of_compactSpace _
      · have : noyauEps (ρ : ℝᵈ → ℝ) 0 = 0 := by
          funext x; simp [noyauEps, zero_pow hd.ne']
        rw [this]; exact HasCompactSupport.zero
    · exact (ρ.hasCompactSupport.comp_smul (inv_ne_zero hε)).mul_left
  tsupport_subset' := by simp

private lemma cdB_integral_lie {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [CompleteSpace M] [NormedAddCommGroup N] [NormedSpace ℝ N] [CompleteSpace N] {X : Type*}
    [MeasurableSpace X] {μ : Measure X} (L : M ≃ₗᵢ[ℝ] N) (f : X → M) :
    ∫ x, L (f x) ∂μ = L (∫ x, f x ∂μ) :=
  L.toLinearIsometry.integral_comp_comm f

private lemma cdB_iteratedFDeriv_conv {φ h : ℝᵈ → ℝ} (hφ : Continuous φ)
    (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h) (i : ℕ) :
    iteratedFDeriv ℝ i (φ ⋆[lsmul ℝ ℝ] h) = fun y => ∫ t, φ t • iteratedFDeriv ℝ i h (y - t) := by
  induction i with
  | zero =>
    funext y
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, convolution_def,
      ← cdB_integral_lie]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    ext v
    simp [iteratedFDeriv_zero_eq_comp]
  | succ i ih =>
    funext y
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
    have hD : ContDiff ℝ 1 (iteratedFDeriv ℝ i h) :=
      hh.iteratedFDeriv_right (by exact_mod_cast le_top)
    have key := (hhc.iteratedFDeriv i).hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      (hφ.locallyIntegrable (μ := volume)) hD y
    have e : (fun y => ∫ t, φ t • iteratedFDeriv ℝ i h (y - t)) =
        φ ⋆[lsmul ℝ ℝ] iteratedFDeriv ℝ i h := by
      funext z; rw [convolution_def]; rfl
    rw [e, key.fderiv, convolution_def,
      ← cdB_integral_lie (M := ℝᵈ →L[ℝ] ℝᵈ [×i]→L[ℝ] ℝ) (N := ℝᵈ [×i + 1]→L[ℝ] ℝ)]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ← map_smul]
    congr 1

private lemma cdB_translRefl_eq (ρ : 𝓓ᵈ) (x : ℝᵈ) :
    (translRefl ρ x : ℝᵈ → ℝ) = fun y => reflTest ρ (y - x) := by
  funext y
  change ρ (x - y) = ρ (-(y - x))
  rw [neg_sub]

private lemma cdB_iteratedFDeriv_translRefl (ρ : 𝓓ᵈ) (x y : ℝᵈ) (i : ℕ) :
    iteratedFDeriv ℝ i (translRefl ρ x) y = iteratedFDeriv ℝ i (reflTest ρ) (y - x) := by
  rw [cdB_translRefl_eq, iteratedFDeriv_comp_sub]

private lemma cdB_convolTest_eq (ψ φ : 𝓓ᵈ) :
    (convolTest ψ φ : ℝᵈ → ℝ) = (φ : ℝᵈ → ℝ) ⋆[lsmul ℝ ℝ] ψ := by
  have h : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    ext; simp
  change (ψ : ℝᵈ → ℝ) ⋆[lsmul ℝ ℝ] φ = _
  rw [← convolution_flip, h]

private lemma cdB_continuous_transl {M : Type*} [NormedAddCommGroup M] {g : ℝᵈ → M}
    (hg : Continuous g) (hgc : HasCompactSupport g) (G : ℝᵈ → BoundedContinuousFunction ℝᵈ M)
    (hG : ∀ x y, G x y = g (y - x)) : Continuous G := by
  have hu := Metric.uniformContinuous_iff.1 (hgc.uniformContinuous_of_continuous hg)
  refine Metric.continuous_iff.2 fun x ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun x' hx' => ?_⟩
  refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (half_pos hε).le).2 fun y => ?_)
    (half_lt_self hε)
  rw [hG, hG]
  exact (h (by rwa [dist_sub_left])).le

private lemma cdB_hahnBanach {V E : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ι : V →ₗ[ℝ] E) (hinj : Function.Injective ι) (T : V →ₗ[ℝ] ℝ) (C : ℝ)
    (hC : ∀ v, ‖T v‖ ≤ C * ‖ι v‖) : ∃ Λ : E →L[ℝ] ℝ, ∀ v, Λ (ι v) = T v := by
  let e := LinearEquiv.ofInjective ι hinj
  let f₀ : LinearMap.range ι →ₗ[ℝ] ℝ := T ∘ₗ e.symm.toLinearMap
  have hf₀ : ∀ v, ‖f₀ v‖ ≤ C * ‖v‖ := by
    intro v
    have hv : (v : E) = ι (e.symm v) := by
      conv_lhs => rw [← e.apply_symm_apply v]
      rfl
    rw [← Submodule.norm_coe, hv]
    exact hC _
  obtain ⟨Λ, hΛ, -⟩ := exists_extension_norm_eq _ (f₀.mkContinuous C hf₀)
  refine ⟨Λ, fun v => ?_⟩
  have h1 := hΛ (e v)
  rw [LinearMap.mkContinuous_apply] at h1
  have h2 : ((e v : LinearMap.range ι) : E) = ι v := rfl
  rw [h2] at h1
  rw [h1]
  simp [f₀]

private lemma cdB_core {n : ℕ} {M : Fin n → Type*} [∀ i, NormedAddCommGroup (M i)]
    [∀ i, NormedSpace ℝ (M i)] [∀ i, CompleteSpace (M i)]
    (Λ : (Π i, BoundedContinuousFunction ℝᵈ (M i)) →L[ℝ] ℝ) {φ : ℝᵈ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) {G : ℝᵈ → Π i, BoundedContinuousFunction ℝᵈ (M i)}
    (hG : Continuous G) (v : Π i, BoundedContinuousFunction ℝᵈ (M i))
    (hv : ∀ i y, ∫ x, φ x • G x i y = v i y) :
    ∫ x, φ x * Λ (G x) = Λ v := by
  have hFi : Integrable (fun x => φ x • G x) :=
    (hφ.smul hG).integrable_of_hasCompactSupport hφc.smul_right
  have hint : ∫ x, φ x • G x = v := by
    funext i
    ext y : 1
    have := ((BoundedContinuousFunction.evalCLM ℝ y).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i => BoundedContinuousFunction ℝᵈ (M i)) i)
      ).integral_comp_comm hFi
    rw [← hv i y]
    simpa using this.symm
  rw [← hint, ← Λ.integral_comp_comm hFi]
  simp

/-- **Prop. `prop:convolDistrib` (Convolution d'une distribution), identité.**
`⟨T ⋆ ρ, φ⟩ = ⟨T, ρ̄ ⋆ φ⟩`, sous la forme `∫ (T ⋆ ρ) φ = ⟨T, ρ̄ ⋆ φ⟩`.
Preuve (différente du cours, qui définit d'abord `T * ρ` par cette formule puis montre que les deux
définitions coïncident) : directe. Sur un compact `K` contenant les supports, `T` est majorée par
`C max_{i ≤ N} ‖Dⁱ ·‖_∞` ; par Hahn–Banach elle se prolonge en une forme continue `Λ` sur un
produit fini d'espaces de fonctions continues bornées, où `x ↦ φ(x) (Dⁱρ(x - ·))_{i ≤ N}` est
intégrable au sens de Bochner, d'intégrale `(Dⁱ(ρ̄ ⋆ φ))_{i ≤ N}` ; `Λ` commute avec l'intégrale. -/
theorem prop_convolDistrib_integral (T : 𝓓'ᵈ) (ρ φ : 𝓓ᵈ) :
    ∫ x, convolDistrib T ρ x * φ x = T (convolTest (reflTest ρ) φ) := by
  classical
  -- a radius controlling the supports of `ρ` and `φ`
  obtain ⟨R₁, hR₁⟩ := ρ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  set R := max (max R₁ R₂) 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  have hρR : tsupport ρ ⊆ Metric.closedBall 0 R :=
    hR₁.trans (Metric.closedBall_subset_closedBall ((le_max_left _ _).trans (le_max_left _ _)))
  have hφR : tsupport φ ⊆ Metric.closedBall 0 R :=
    hR₂.trans (Metric.closedBall_subset_closedBall ((le_max_right _ _).trans (le_max_left _ _)))
  let K : Compacts ℝᵈ := ⟨Metric.closedBall 0 (R + R), isCompact_closedBall _ _⟩
  have hKΩ : (K : Set ℝᵈ) ⊆ ((⊤ : Opens ℝᵈ) : Set ℝᵈ) := fun _ _ => trivial
  let TK : 𝓓_{K}(ℝᵈ, ℝ) →L[ℝ] ℝ := T.comp (TestFunction.ofSupportedInCLM ℝ hKΩ)
  -- the continuity estimate of `T` on `𝓓_K`
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous
    (ContDiffMapSupportedIn.withSeminorms ℝ ℝᵈ ℝ ⊤ K) ((normSeminorm ℝ ℝ).comp TK.toLinearMap)
    (continuous_norm.comp TK.continuous)
  set N := s.sup id
  have : ∀ i : Fin (N + 1), ContinuousAdd (ℝᵈ [×i]→L[ℝ] ℝ) := fun i => inferInstance
  let ι : 𝓓_{K}(ℝᵈ, ℝ) →L[ℝ] Π i : Fin (N + 1), BoundedContinuousFunction ℝᵈ (ℝᵈ [×i]→L[ℝ] ℝ) :=
    ContinuousLinearMap.pi fun i => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ)
  have hbound : ∀ ψ, ‖TK ψ‖ ≤ C * ‖ι ψ‖ := by
    intro ψ
    calc ‖TK ψ‖ = ((normSeminorm ℝ ℝ).comp TK.toLinearMap) ψ := rfl
      _ ≤ (C • s.sup (ContDiffMapSupportedIn.seminorm ℝ ℝᵈ ℝ ⊤ K)) ψ := hC ψ
      _ = C * s.sup (ContDiffMapSupportedIn.seminorm ℝ ℝᵈ ℝ ⊤ K) ψ := rfl
      _ ≤ C * ‖ι ψ‖ := by
        gcongr
        refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun i hi => ?_
        have hiN : i < N + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)
        exact norm_le_pi_norm (ι ψ) ⟨i, hiN⟩
  have hinj : Function.Injective ι := fun a b hab =>
    ContDiffMapSupportedIn.structureMapCLM_zero_injective ℝ (congrFun hab 0)
  obtain ⟨Λ, hΛι⟩ := cdB_hahnBanach
    (E := Π i : Fin (N + 1), BoundedContinuousFunction ℝᵈ (ℝᵈ [×i]→L[ℝ] ℝ))
    ι.toLinearMap hinj TK.toLinearMap C (fun ψ => hbound ψ)
  -- the `E`-valued integrand `x ↦ φ x • ι (ρ (x - ·))`, written globally
  set ρb := reflTest ρ with hρb
  let Kb : Compacts ℝᵈ := ⟨tsupport ρb, ρb.hasCompactSupport⟩
  let ρK : 𝓓_{Kb}(ℝᵈ, ℝ) := ContDiffMapSupportedIn.of_support_subset ρb.contDiff subset_closure
  let G : ℝᵈ → Π i : Fin (N + 1), BoundedContinuousFunction ℝᵈ (ℝᵈ [×i]→L[ℝ] ℝ) :=
    fun x i => (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ (i : ℕ) ρK).compContinuous
      ⟨fun y => y - x, by fun_prop⟩
  have hG : ∀ x (i : Fin (N + 1)) y, G x i y = iteratedFDeriv ℝ i ρb (y - x) := by
    intro x i y
    simp [G]
    rfl
  have hGc : Continuous G := continuous_pi fun i =>
    cdB_continuous_transl (ρb.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top))
      (ρb.hasCompactSupport.iteratedFDeriv _) (fun x => G x i) (fun x y => hG x i y)
  -- pointwise: `Λ (G x) = (T ⋆ ρ)(x)` on the support of `φ`
  have hΛG : ∀ x, φ x * Λ (G x) = convolDistrib T ρ x * φ x := by
    intro x
    by_cases hx : φ x = 0
    · simp [hx]
    have hxR : x ∈ Metric.closedBall (0 : ℝᵈ) R := hφR (subset_tsupport _ hx)
    have hsupp : Function.support (translRefl ρ x) ⊆ K := by
      intro y hy
      have h1 : x - y ∈ Metric.closedBall (0 : ℝᵈ) R := hρR (subset_tsupport _ hy)
      rw [Metric.mem_closedBall, dist_zero_right] at h1 hxR
      change y ∈ Metric.closedBall (0 : ℝᵈ) (R + R)
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖y‖ = ‖x - (x - y)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add hxR h1
    let τ : 𝓓_{K}(ℝᵈ, ℝ) :=
      ContDiffMapSupportedIn.of_support_subset (translRefl ρ x).contDiff hsupp
    have hGτ : G x = ι τ := by
      funext i
      ext y : 1
      rw [hG]
      simp only [ι, ContinuousLinearMap.pi_apply,
        ContDiffMapSupportedIn.structureMapCLM_top_apply]
      exact (cdB_iteratedFDeriv_translRefl ρ x y i).symm
    have hτ : TestFunction.ofSupportedIn hKΩ τ = translRefl ρ x := TestFunction.ext fun _ => rfl
    rw [hGτ, show Λ (ι τ) = TK τ from hΛι τ, mul_comm]
    change T (TestFunction.ofSupportedIn hKΩ τ) * φ x = T (translRefl ρ x) * φ x
    rw [hτ]
  -- `ρ̄ ⋆ φ` as an element of `𝓓_K`
  have hsuppC : Function.support (convolTest ρb φ) ⊆ K := by
    change Function.support ((ρb : ℝᵈ → ℝ) ⋆[lsmul ℝ ℝ] φ) ⊆ Metric.closedBall 0 (R + R)
    refine (support_convolution_subset _).trans ?_
    have h1 : Function.support ρb ⊆ Metric.closedBall (0 : ℝᵈ) R := fun y hy => by
      have : -y ∈ Metric.closedBall (0 : ℝᵈ) R := hρR (subset_tsupport ρ hy)
      simpa using this
    have h2 : Function.support φ ⊆ Metric.closedBall (0 : ℝᵈ) R := (subset_tsupport _).trans hφR
    refine (Set.add_subset_add h1 h2).trans ?_
    rw [closedBall_add_closedBall hR0 hR0, add_zero]
  let ψK : 𝓓_{K}(ℝᵈ, ℝ) :=
    ContDiffMapSupportedIn.of_support_subset (convolTest ρb φ).contDiff hsuppC
  have hψK : TestFunction.ofSupportedIn hKΩ ψK = convolTest ρb φ := TestFunction.ext fun _ => rfl
  have hv : ∀ (i : Fin (N + 1)) y, ∫ x, φ x • G x i y = ι ψK i y := by
    intro i y
    simp only [ι, ContinuousLinearMap.pi_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    change _ = iteratedFDeriv ℝ i (convolTest ρb φ) y
    rw [cdB_convolTest_eq, cdB_iteratedFDeriv_conv φ.continuous ρb.contDiff ρb.hasCompactSupport]
    simp only [hG]
  calc ∫ x, convolDistrib T ρ x * φ x = ∫ x, φ x * Λ (G x) := by simp_rw [hΛG]
    _ = Λ (ι ψK) := cdB_core Λ φ.continuous φ.hasCompactSupport hGc (ι ψK) hv
    _ = T (convolTest (reflTest ρ) φ) := by
      rw [show Λ (ι ψK) = TK ψK from hΛι ψK]
      change T (TestFunction.ofSupportedIn hKΩ ψK) = _
      rw [hψK]

/-- Continuity of `T ⋆ ρ`, from the continuity of `x ↦ ρ (x - ·)` into `𝓓_K` on balls. -/
private lemma cdB_continuous_convolDistrib (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) :
    Continuous (convolDistrib T ρ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨R, hR⟩ := ρ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  let K : Compacts ℝᵈ := ⟨Metric.closedBall 0 (‖x₀‖ + 1 + R), isCompact_closedBall _ _⟩
  have hKΩ : (K : Set ℝᵈ) ⊆ ((⊤ : Opens ℝᵈ) : Set ℝᵈ) := fun _ _ => trivial
  have hsupp : ∀ x ∈ Metric.ball x₀ 1, Function.support (translRefl ρ x) ⊆ K := by
    intro x hx y hy
    have h1 : x - y ∈ Metric.closedBall (0 : ℝᵈ) R := hR (subset_tsupport _ hy)
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    rw [Metric.mem_ball, dist_eq_norm] at hx
    change y ∈ Metric.closedBall (0 : ℝᵈ) (‖x₀‖ + 1 + R)
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖y‖ = ‖x₀ + (x - x₀) - (x - y)‖ := by congr 1; abel
      _ ≤ ‖x₀‖ + ‖x - x₀‖ + ‖x - y‖ := (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ ‖x₀‖ + 1 + R := by gcongr
  let σ : Metric.ball x₀ 1 → 𝓓_{K}(ℝᵈ, ℝ) := fun x =>
    ContDiffMapSupportedIn.of_support_subset (translRefl ρ x).contDiff (hsupp x x.2)
  set ρb := reflTest ρ with hρb
  let Kb : Compacts ℝᵈ := ⟨tsupport ρb, ρb.hasCompactSupport⟩
  let ρK : 𝓓_{Kb}(ℝᵈ, ℝ) := ContDiffMapSupportedIn.of_support_subset ρb.contDiff subset_closure
  have hσ : Continuous σ := by
    rw [ContDiffMapSupportedIn.continuous_iff_comp]
    intro i
    let G : ℝᵈ → BoundedContinuousFunction ℝᵈ (ℝᵈ [×i]→L[ℝ] ℝ) := fun x =>
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ρK).compContinuous
        ⟨fun y => y - x, by fun_prop⟩
    have hG : ∀ x y, G x y = iteratedFDeriv ℝ i ρb (y - x) := by
      intro x y
      simp [G]
      rfl
    have hGc : Continuous G :=
      cdB_continuous_transl (ρb.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top))
        (ρb.hasCompactSupport.iteratedFDeriv _) G hG
    have hcomp : ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ σ = G ∘ Subtype.val := by
      funext x
      ext y : 1
      simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply, hG]
      exact cdB_iteratedFDeriv_translRefl ρ x y i
    rw [hcomp]
    exact hGc.comp continuous_subtype_val
  have hc : Continuous (fun x : Metric.ball x₀ 1 => convolDistrib T ρ x) := by
    refine ((T.continuous.comp (TestFunction.continuous_ofSupportedIn hKΩ)).comp hσ).congr
      fun x => ?_
    change T (TestFunction.ofSupportedIn hKΩ (σ x)) = T (translRefl ρ x)
    congr 1
  exact (continuousOn_iff_continuous_domRestrict.2 hc).continuousAt
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

/-- **Prop. `prop:convolDistrib`, identité**, via la distribution `U_{T⋆ρ}` associée à la
fonction continue (donc localement intégrable) `T ⋆ ρ` (`Distribution.ofFun`) :
`⟨U_{T⋆ρ}, φ⟩ = ⟨T, ρ̄ ⋆ φ⟩`. -/
theorem prop_convolDistrib_ofFun (T : 𝓓'ᵈ) (ρ φ : 𝓓ᵈ) :
    Distribution.ofFun ⊤ (convolDistrib T ρ) volume ⊤ φ = T (convolTest (reflTest ρ) φ) := by
  have hli : LocallyIntegrableOn (convolDistrib T ρ) ((⊤ : Opens ℝᵈ) : Set ℝᵈ) volume :=
    (cdB_continuous_convolDistrib T ρ).locallyIntegrable.locallyIntegrableOn _
  rw [Distribution.ofFun_apply hli, ← prop_convolDistrib_integral]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [mul_comm]

private lemma cdA_lineDeriv_apply (ψ : 𝓓ᵈ) (v y : ℝᵈ) :
    (∂_{v} ψ : 𝓓ᵈ) y = fderiv ℝ ψ y v := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_apply_of_le le_top,
    ((ψ.contDiff.differentiable (by simp)) y).lineDeriv_eq_fderiv]

private lemma cdA_iter_apply {n : ℕ} (ψ : 𝓓ᵈ) (u : Fin n → ℝᵈ) (y : ℝᵈ) :
    (∂^{u} ψ : 𝓓ᵈ) y = iteratedFDeriv ℝ n ψ y u := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_left, cdA_lineDeriv_apply,
      iteratedFDeriv_succ_apply_left]
    have : (⇑(∂^{Fin.tail u} ψ : 𝓓ᵈ)) = fun z => iteratedFDeriv ℝ n ψ z (Fin.tail u) :=
      funext (ih _)
    rw [this, fderiv_continuousMultilinear_apply_const_apply]
    exact (ψ.contDiff.differentiable_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top n)).differentiableAt

private lemma cdA_comm {n : ℕ} (ρ : 𝓓ᵈ) (u : Fin n → ℝᵈ) (h : ℝᵈ) :
    (∂^{u} (∂_{h} ρ) : 𝓓ᵈ) = ∂_{h} (∂^{u} ρ) := by
  have h1 : (∂^{u} (∂_{h} ρ) : 𝓓ᵈ) = ∂^{Fin.snoc u h} ρ := by
    rw [LineDeriv.iteratedLineDerivOp_succ_right, Fin.init_snoc, Fin.snoc_last]
  have h2 : (∂_{h} (∂^{u} ρ) : 𝓓ᵈ) = ∂^{Fin.cons h u} ρ := by
    rw [LineDeriv.iteratedLineDerivOp_succ_left, Fin.tail_cons, Fin.cons_zero]
  rw [h1, h2]
  ext y
  rw [cdA_iter_apply, cdA_iter_apply, ← Fin.insertNth_last', ← Fin.cons_comp_cycleRange]
  exact iteratedFDeriv_comp_perm_of_contDiff (n + 1) (ρ.contDiff.of_le (by exact_mod_cast le_top))
    y _ _

private lemma cdA_lineDeriv_translRefl (σ : 𝓓ᵈ) (x v : ℝᵈ) :
    (∂_{v} (translRefl σ x) : 𝓓ᵈ) = -translRefl (∂_{v} σ) x := by
  ext y
  rw [cdA_lineDeriv_apply, IsNegApply.neg_apply, translRefl_apply, cdA_lineDeriv_apply]
  have hσ : DifferentiableAt ℝ σ (x - y) := (σ.contDiff.differentiable (by simp)) _
  have hd := hσ.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  have : (⇑(translRefl σ x)) = ⇑σ ∘ HSub.hSub x := rfl
  rw [this, hd.fderiv]
  simp

private lemma cdA_iter_translRefl {n : ℕ} (σ : 𝓓ᵈ) (x : ℝᵈ) (u : Fin n → ℝᵈ) :
    (∂^{u} (translRefl σ x) : 𝓓ᵈ) = ((-1 : ℝ) ^ n) • translRefl (∂^{u} σ) x := by
  induction n generalizing σ with
  | zero => simp
  | succ n ih =>
    rw [LineDeriv.iteratedLineDerivOp_succ_right, cdA_lineDeriv_translRefl,
      LineDeriv.iteratedLineDerivOp_neg, ih, LineDeriv.iteratedLineDerivOp_succ_right u σ,
      pow_succ, mul_neg_one, neg_smul]

private lemma cdA_bound (T : 𝓓'ᵈ) {K : Set ℝᵈ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ ψ : 𝓓ᵈ, tsupport ψ ⊆ K → ∀ M : ℝ, 0 ≤ M →
      (∀ i ≤ N, ∀ w : Fin i → Fin d, ∀ y,
        |(∂^{fun k => EuclideanSpace.single (w k) (1 : ℝ)} ψ : 𝓓ᵈ) y| ≤ M) →
      |T ψ| ≤ C * M := by
  obtain ⟨C, n, hC⟩ := (def_distribution ⊤ (T : 𝓓ᵈ →ₗ[ℝ] ℝ)).1 T.continuous K hK (by simp)
  refine ⟨max C 0, le_max_right _ _, n, fun ψ hψ M hM h => ?_⟩
  have hN : normeK K n ψ ≤ M := normeK_le hM fun y _ α hα => by
    rw [← congrFun (coe_iteratedLineDeriv_testFunction ⊤ α ψ) y]
    exact h _ (by rw [length_directions]; exact hα) (directions α).get y
  calc |T ψ| ≤ C * normeK K n ψ := hC ψ hψ
    _ ≤ max C 0 * normeK K n ψ := by
      gcongr
      · exact normeK_nonneg _ _ _
      · exact le_max_left _ _
    _ ≤ max C 0 * M := by gcongr

private lemma cdA_taylor (σ : 𝓓ᵈ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h in 𝓝 (0 : ℝᵈ), ∀ z, |σ (z + h) - σ z - (∂_{h} σ : 𝓓ᵈ) z| ≤ ε * ‖h‖ := by
  have hσ : ContDiff ℝ 1 σ := σ.contDiff.of_le (by exact_mod_cast le_top)
  have huc : UniformContinuous (fderiv ℝ σ) :=
    (σ.hasCompactSupport.fderiv ℝ).uniformContinuous_of_continuous
      (hσ.continuous_fderiv one_ne_zero)
  obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuous_iff.1 huc ε hε
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with h hh z
  have hdiff : Differentiable ℝ σ := hσ.differentiable one_ne_zero
  set g : ℝᵈ → ℝ := fun w => σ w - fderiv ℝ σ z w with hg
  have hgd : ∀ w, HasFDerivAt g (fderiv ℝ σ w - fderiv ℝ σ z) w := fun w =>
    (hdiff w).hasFDerivAt.sub (fderiv ℝ σ z).hasFDerivAt
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := g) (C := ε)
    (s := segment ℝ z (z + h)) (fun w _ => (hgd w).differentiableAt)
    (fun w hw => by
      rw [(hgd w).fderiv, ← dist_eq_norm]
      refine (H ?_).le
      have h1 := segment_subset_closedBall_left z (z + h) hw
      rw [Metric.mem_closedBall] at h1
      refine h1.trans_lt ?_
      rw [Metric.mem_ball, dist_zero_right] at hh
      rwa [dist_eq_norm, sub_add_cancel_left, norm_neg])
    (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
  rw [cdA_lineDeriv_apply, ← Real.norm_eq_abs]
  convert key using 2
  · simp only [hg, map_add]; ring
  · simp

private lemma cdA_translRefl_add (a b : 𝓓ᵈ) (x : ℝᵈ) :
    translRefl (a + b) x = translRefl a x + translRefl b x := by
  ext y; simp

private lemma cdA_translRefl_smul (c : ℝ) (a : 𝓓ᵈ) (x : ℝᵈ) :
    translRefl (c • a) x = c • translRefl a x := by
  ext y; simp

private lemma cdA_norm_le {σ : 𝓓ᵈ} {R : ℝ} (hR : tsupport σ ⊆ Metric.closedBall 0 R)
    {z y : ℝᵈ} (hy : σ (z - y) ≠ 0) : ‖y‖ ≤ ‖z‖ + R := by
  have hm := hR (subset_tsupport _ hy)
  rw [Metric.mem_closedBall, dist_zero_right] at hm
  calc ‖y‖ = ‖z - (z - y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖z‖ + ‖z - y‖ := norm_sub_le _ _
    _ ≤ ‖z‖ + R := by gcongr

private lemma cdA_hasFDerivAt (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) (x : ℝᵈ) :
    ∃ L : ℝᵈ →L[ℝ] ℝ, HasFDerivAt (convolDistrib T ρ) L x ∧
      ∀ v, L v = convolDistrib T (∂_{v} ρ) x := by
  let Lin : ℝᵈ →ₗ[ℝ] ℝ :=
    { toFun := fun v => convolDistrib T (∂_{v} ρ) x
      map_add' := fun v w => by
        simp only [convolDistrib, LineDerivAdd.lineDerivOp_left_add, cdA_translRefl_add, map_add]
      map_smul' := fun c v => by
        simp only [convolDistrib, LineDerivLeftSMul.lineDerivOp_left_smul, cdA_translRefl_smul,
          map_smul, smul_eq_mul, RingHom.id_apply] }
  refine ⟨LinearMap.toContinuousLinearMap Lin, ?_, fun v => rfl⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨R, hR⟩ := ρ.hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨C, hC0, N, hB⟩ := cdA_bound T (isCompact_closedBall (0 : ℝᵈ) (‖x‖ + 1 + R))
  have hε : 0 < c / (C + 1) := by positivity
  have hev : ∀ᶠ h in 𝓝 (0 : ℝᵈ), ‖h‖ ≤ 1 ∧ ∀ i : Fin (N + 1), ∀ w : Fin i → Fin d, ∀ z,
      |(∂^{fun k => EuclideanSpace.single (w k) (1 : ℝ)} ρ : 𝓓ᵈ) (z + h)
        - (∂^{fun k => EuclideanSpace.single (w k) (1 : ℝ)} ρ : 𝓓ᵈ) z
        - (∂_{h} (∂^{fun k => EuclideanSpace.single (w k) (1 : ℝ)} ρ) : 𝓓ᵈ) z|
        ≤ c / (C + 1) * ‖h‖ := by
    refine Filter.Eventually.and ?_ ?_
    · filter_upwards [Metric.closedBall_mem_nhds (0 : ℝᵈ) one_pos] with h hh
      simpa using hh
    · rw [Filter.eventually_all]
      intro i
      rw [Filter.eventually_all]
      intro w
      exact cdA_taylor _ hε
  filter_upwards [hev] with h ⟨h1, h2⟩
  set ψ : 𝓓ᵈ := translRefl ρ (x + h) - translRefl ρ x - translRefl (∂_{h} ρ) x with hψ
  have hval : convolDistrib T ρ (x + h) - convolDistrib T ρ x
      - (LinearMap.toContinuousLinearMap Lin) h = T ψ := by
    simp only [hψ, map_sub]
    rfl
  rw [hval, Real.norm_eq_abs]
  have hRd : tsupport (∂_{h} ρ : 𝓓ᵈ) ⊆ Metric.closedBall 0 R := by
    refine closure_minimal (fun z hz => hR ?_) Metric.isClosed_closedBall
    by_contra hz'
    exact hz (by rw [cdA_lineDeriv_apply, fderiv_of_notMem_tsupport ℝ hz']; rfl)
  have hsupp : tsupport ψ ⊆ Metric.closedBall 0 (‖x‖ + 1 + R) := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hlt
    push Not at hlt
    have hxh : ‖x + h‖ ≤ ‖x‖ + 1 := (norm_add_le _ _).trans (by gcongr)
    have e1 : ρ (x + h - y) = 0 := by
      by_contra hne
      have := cdA_norm_le hR hne
      linarith
    have e2 : ρ (x - y) = 0 := by
      by_contra hne
      have := cdA_norm_le hR hne
      linarith [norm_nonneg h]
    have e3 : (∂_{h} ρ : 𝓓ᵈ) (x - y) = 0 := by
      by_contra hne
      have := cdA_norm_le hRd hne
      linarith [norm_nonneg h]
    exact hy (by simp [hψ, e1, e2, e3])
  have hbd := hB ψ hsupp (c / (C + 1) * ‖h‖) (by positivity) (fun i hi w y => ?_)
  · calc |T ψ| ≤ C * (c / (C + 1) * ‖h‖) := hbd
      _ ≤ c * ‖h‖ := by
        rw [← mul_assoc]
        gcongr
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
  · have := h2 ⟨i, Nat.lt_succ_of_le hi⟩ w (x - y)
    simp only [hψ, sub_eq_add_neg, LineDeriv.iteratedLineDerivOp_add,
      LineDeriv.iteratedLineDerivOp_neg, cdA_iter_translRefl, cdA_comm, IsAddApply.add_apply,
      IsNegApply.neg_apply, IsSMulApply.smul_apply, translRefl_apply, smul_eq_mul]
    rw [show x + h + -y = x - y + h by abel, show x + -y = x - y by abel]
    refine Eq.trans_le ?_ this
    rw [← mul_neg, ← mul_neg, ← mul_add, ← mul_add, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, ← sub_eq_add_neg, ← sub_eq_add_neg]

private lemma cdA_fderiv_apply (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) (x v : ℝᵈ) :
    fderiv ℝ (convolDistrib T ρ) x v = convolDistrib T (∂_{v} ρ) x := by
  obtain ⟨L, hL, hLv⟩ := cdA_hasFDerivAt T ρ x
  rw [hL.fderiv, hLv]

private lemma cdA_differentiable (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) : Differentiable ℝ (convolDistrib T ρ) :=
  fun x => (cdA_hasFDerivAt T ρ x).choose_spec.1.differentiableAt

private lemma cdA_contDiff (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) : ContDiff ℝ ∞ (convolDistrib T ρ) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing ρ with
  | zero => exact contDiff_zero.2 (cdA_differentiable T ρ).continuous
  | succ n ih =>
    have hrep : ∀ v : ℝᵈ, v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := fun v => by
      ext m
      simp [Pi.single_apply]
    have hf : fderiv ℝ (convolDistrib T ρ) = fun x => ∑ i,
        convolDistrib T (∂_{EuclideanSpace.single i (1 : ℝ)} ρ) x • EuclideanSpace.proj i := by
      funext x
      ext v
      conv_lhs => rw [hrep v]
      simp [map_sum, cdA_fderiv_apply, mul_comm]
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨cdA_differentiable T ρ, by simp, ?_⟩
    rw [hf]
    exact ContDiff.sum fun i _ => (ih _).smul contDiff_const

/-- **Prop. `prop:convolDistrib` (i).** `T ⋆ ρ ∈ C^∞(ℝ^d)`.
Preuve (différente du cours, qui passe par « dérivées dans `L^∞_loc` ⇒ `C^∞` ») : directe, par
`hasFDerivAt_convolDistrib` (la différentielle est encore une convolée `T ⋆ ∂_v ρ`) et
récurrence. -/
theorem prop_convolDistrib_contDiff (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) :
    ContDiff ℝ ∞ (convolDistrib T ρ) := by
  exact cdA_contDiff T ρ

/-- **Prop. `prop:convolDistrib` (i)-(ii), lemme clé.** `T ⋆ ρ` est différentiable, de
différentielle `v ↦ (T ⋆ ∂_v ρ)(x)`. Preuve : le reste `ρ(x+h-·) - ρ(x-·) - ∂_h ρ(x-·)` est à
support dans un compact fixe, et ses dérivées d'ordre `≤ N` sont `o(‖h‖)` uniformément (Taylor et
continuité uniforme) ; on conclut par la continuité de `T` sur `𝓓_K`. -/
theorem hasFDerivAt_convolDistrib (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) (x : ℝᵈ) :
    ∃ L : ℝᵈ →L[ℝ] ℝ, HasFDerivAt (convolDistrib T ρ) L x ∧
      ∀ v, L v = convolDistrib T (∂_{v} ρ) x := by
  exact cdA_hasFDerivAt T ρ x

/-- **Prop. `prop:convolDistrib` (ii), dérivées directionnelles.**
`∂_v (T ⋆ ρ) = (∂_v T) ⋆ ρ = T ⋆ ∂_v ρ`. -/
theorem prop_convolDistrib_lineDeriv (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) (v x : ℝᵈ) :
    fderiv ℝ (convolDistrib T ρ) x v = convolDistrib (∂_{v} T) ρ x ∧
      fderiv ℝ (convolDistrib T ρ) x v = convolDistrib T (∂_{v} ρ) x := by
  refine ⟨?_, cdA_fderiv_apply T ρ x v⟩
  rw [cdA_fderiv_apply]
  simp only [convolDistrib]
  rw [Distribution.lineDerivOp_apply_apply, cdA_lineDeriv_translRefl]
  simp

private lemma cdA_iteratedFDeriv (T : 𝓓'ᵈ) {n : ℕ} (u : Fin n → ℝᵈ) (ρ : 𝓓ᵈ) (x : ℝᵈ) :
    iteratedFDeriv ℝ n (convolDistrib T ρ) x u = convolDistrib T (∂^{u} ρ) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedFDeriv_succ_apply_left, ← fderiv_continuousMultilinear_apply_const_apply
      (((cdA_contDiff T ρ).differentiable_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top n)) x)]
    have : (fun y => iteratedFDeriv ℝ n (convolDistrib T ρ) y (Fin.tail u)) =
        convolDistrib T (∂^{Fin.tail u} ρ) := funext (ih _)
    rw [this, cdA_fderiv_apply, LineDeriv.iteratedLineDerivOp_succ_left]

/-- **Prop. `prop:convolDistrib` (ii).** `∂_α (T ⋆ ρ) = (∂_α T) ⋆ ρ = T ⋆ ∂_α ρ` pour tout
multi-indice `α` (`deriveePartielle`, `deriveeDistrib`). -/
theorem prop_convolDistrib_deriv (T : 𝓓'ᵈ) (ρ : 𝓓ᵈ) (α : Fin d → ℕ) :
    deriveePartielle α (convolDistrib T ρ) = convolDistrib (deriveeDistrib ⊤ α T) ρ ∧
      deriveePartielle α (convolDistrib T ρ) = convolDistrib T (∂^{dirMulti α} ρ) := by
  have h2 : deriveePartielle α (convolDistrib T ρ) = convolDistrib T (∂^{dirMulti α} ρ) :=
    funext fun x => cdA_iteratedFDeriv T (dirMulti α) ρ x
  refine ⟨?_, h2⟩
  rw [h2]
  funext x
  simp only [convolDistrib]
  rw [prop_deriv_distrib_apply, cdA_iter_translRefl, map_smul, smul_eq_mul,
    show ((-1 : ℝ) ^ (directions α).length) = (-1) ^ ∑ i, α i by rw [length_directions],
    ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

private lemma cdC_supp {ρ : ℝᵈ → ℝ} {R ε : ℝ} (hR : Function.support ρ ⊆ Metric.closedBall 0 R)
    (hε : 0 < ε) {t : ℝᵈ} (ht : noyauEps ρ ε t ≠ 0) : ‖t‖ ≤ ε * R := by
  have h1 : ρ (ε⁻¹ • t) ≠ 0 := fun h => ht (by simp [noyauEps, h])
  have h2 := hR h1
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le),
    inv_mul_le_iff₀ hε] at h2
  exact h2

private lemma cdC_integral_abs (ρ : ℝᵈ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t, |noyauEps ρ ε t| = ∫ t, |ρ t| := by
  have : (fun t => |noyauEps ρ ε t|) = noyauEps (fun x => |ρ x|) ε := by
    funext t
    simp [noyauEps, abs_mul, abs_of_pos (pow_pos hε d)]
  rw [this, integral_noyauEps hε]

private lemma cdC_est {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {ρ : ℝᵈ → ℝ} (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) {R ε η : ℝ}
    (hR : Function.support ρ ⊆ Metric.closedBall 0 R) (hε : 0 < ε)
    {g : ℝᵈ → G} (hg : Continuous g) (hgs : HasCompactSupport g)
    (hη : ∀ x t, ‖t‖ ≤ ε * R → ‖g (x - t) - g x‖ ≤ η) (x : ℝᵈ) :
    ‖(noyauEps ρ ε ⋆[lsmul ℝ ℝ] g) x - (∫ t, ρ t) • g x‖ ≤ (∫ t, |ρ t|) * η := by
  have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport hρs
  have hki : Integrable (noyauEps ρ ε) := integrable_noyauEps hρi hε
  have h1 : Integrable (fun t => noyauEps ρ ε t • g (x - t)) :=
    hgs.convolutionExists_right (lsmul ℝ ℝ) hki.locallyIntegrable hg x
  have h2 : Integrable (fun t => noyauEps ρ ε t • g x) := hki.smul_const _
  rw [convolution_def, ← integral_noyauEps (ρ := ρ) hε, ← integral_smul_const]
  simp only [ContinuousLinearMap.lsmul_apply]
  rw [← integral_sub h1 h2, ← cdC_integral_abs ρ hε, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hki.abs.mul_const _) (ae_of_all _ fun t => ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  by_cases ht : noyauEps ρ ε t = 0
  · simp [ht]
  · exact mul_le_mul_of_nonneg_left (hη x t (cdC_supp hR hε ht)) (abs_nonneg _)

/-- **Corol. `corol:convolTestFun`, cas `Ω = ℝ^d`.** `ρ_ε ⋆ φ → (∫ ρ) φ` dans `𝓓(ℝ^d)` lorsque
`ε → 0⁺`. Preuve : les supports restent dans un compact fixe, et
`Dⁱ(ρ_ε ⋆ φ) = ρ_ε ⋆ Dⁱφ → (∫ ρ) Dⁱφ` uniformément, par continuité uniforme de `Dⁱφ` ; l'estimation
est faite directement pour `ρ` de signe quelconque (le cours sépare parties positive et
négative). -/
theorem corol_convolTestFun (ρ φ : 𝓓ᵈ) :
    Tendsto (fun ε => convolTest (noyauEpsTest ρ ε) φ) (𝓝[>] 0)
      (𝓝 ((∫ x, ρ x) • φ)) := by
  obtain ⟨R, hR0, hR⟩ := ρ.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  have hRs : Function.support (ρ : ℝᵈ → ℝ) ⊆ Metric.closedBall 0 R :=
    (subset_tsupport _).trans hR
  obtain ⟨r, hr0, hr⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall_lt 0 0
  set c := ∫ x, ρ x
  let K : Compacts ℝᵈ := ⟨Metric.closedBall 0 (R + r), isCompact_closedBall 0 (R + r)⟩
  have hsupp : ∀ ε, 0 < ε ∧ ε ≤ 1 →
      EqOn (convolTest (noyauEpsTest ρ ε) φ : ℝᵈ → ℝ) 0 (K : Set ℝᵈ)ᶜ := by
    intro ε hε x hx
    by_contra hne
    have hm : x ∈ Function.support (noyauEps (ρ : ℝᵈ → ℝ) ε ⋆[lsmul ℝ ℝ] (φ : ℝᵈ → ℝ)) := hne
    obtain ⟨a, ha, b, hb, rfl⟩ := support_convolution_subset (lsmul ℝ ℝ) hm
    apply hx
    have h1 : ‖a‖ ≤ ε * R := cdC_supp hRs hε.1 ha
    have h2 : ‖b‖ ≤ r := mem_closedBall_zero_iff.1 (hr (subset_tsupport _ hb))
    change a + b ∈ Metric.closedBall 0 (R + r)
    rw [mem_closedBall_zero_iff]
    calc ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
      _ ≤ R + r := by nlinarith
  let G : ℝ → 𝓓_{K}(ℝᵈ, ℝ) := fun ε => if h : 0 < ε ∧ ε ≤ 1 then
    ⟨convolTest (noyauEpsTest ρ ε) φ, (convolTest (noyauEpsTest ρ ε) φ).contDiff, hsupp ε h⟩
    else 0
  let φK : 𝓓_{K}(ℝᵈ, ℝ) := ⟨φ, φ.contDiff, fun x hx => by
    by_contra hne
    apply hx
    change x ∈ Metric.closedBall 0 (R + r)
    have := hr (subset_tsupport _ hne)
    rw [mem_closedBall_zero_iff] at this ⊢
    linarith⟩
  have hKsub : (K : Set ℝᵈ) ⊆ ((⊤ : Opens ℝᵈ) : Set ℝᵈ) := by simp
  have hG : Tendsto G (𝓝[>] 0) (𝓝 (c • φK)) := by
    rw [(ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM
      ℝ).isInducing.tendsto_nhds_iff, tendsto_pi_nhds]
    intro i
    have hgc : Continuous (iteratedFDeriv ℝ i (φ : ℝᵈ → ℝ)) :=
      φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
    have hgs : HasCompactSupport (iteratedFDeriv ℝ i (φ : ℝᵈ → ℝ)) :=
      φ.hasCompactSupport.iteratedFDeriv i
    have hgu := Metric.uniformContinuous_iff.1 (hgs.uniformContinuous_of_continuous hgc)
    rw [Metric.tendsto_nhds]
    intro η hη
    set A := ∫ t, |ρ t|
    have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
    obtain ⟨δ, hδ, hδu⟩ := hgu (ε := η / (2 * (A + 1))) (by positivity)
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Ioo 0 (min 1 (δ / R)) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hev] with ε hε
    have hε1 : 0 < ε ∧ ε ≤ 1 := ⟨hε.1, (hε.2.trans_le (min_le_left _ _)).le⟩
    have hεR : ε * R < δ := by
      have := hε.2.trans_le (min_le_right _ _)
      rwa [lt_div_iff₀ hR0] at this
    have key := cdC_est ρ.continuous ρ.hasCompactSupport hRs hε1.1 hgc hgs
      (η := η / (2 * (A + 1))) (fun x t ht => by
        have := hδu (a := x - t) (b := x) (by simpa [dist_eq_norm] using ht.trans_lt hεR)
        rw [← dist_eq_norm]; exact this.le)
    have hGe : (G ε : ℝᵈ → ℝ) = noyauEps (ρ : ℝᵈ → ℝ) ε ⋆[lsmul ℝ ℝ] (φ : ℝᵈ → ℝ) := by
      simp only [G, hε1, and_self, dite_true]
      rfl
    have hki : Integrable (noyauEps (ρ : ℝᵈ → ℝ) ε) :=
      integrable_noyauEps (ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport) hε1.1
    have hC : 0 ≤ A * (η / (2 * (A + 1))) := by positivity
    refine lt_of_le_of_lt ((BoundedContinuousFunction.dist_le hC).2 fun x => ?_) ?_
    · simp only [Function.comp_apply, ContinuousLinearMap.pi_apply,
        ContDiffMapSupportedIn.structureMapCLM_top_apply]
      rw [dist_eq_norm, hGe, iteratedFDeriv_convolution hki (φ.contDiff.of_le (by
        exact_mod_cast le_top)) φ.hasCompactSupport le_rfl]
      have hc : (⇑(c • φK) : ℝᵈ → ℝ) = c • (φ : ℝᵈ → ℝ) := rfl
      rw [hc, iteratedFDeriv_const_smul_apply
        ((φ.contDiff.of_le (by exact_mod_cast le_top)).contDiffAt)]
      exact key x
    · have h2 : A * (η / (2 * (A + 1))) = η * (A / (2 * (A + 1))) := by ring
      have h3 : A / (2 * (A + 1)) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith
      rw [h2]
      exact mul_lt_of_lt_one_right hη h3
  have H := ((TestFunction.continuous_ofSupportedIn hKsub).tendsto _).comp hG
  have hlim : TestFunction.ofSupportedIn hKsub (c • φK) = c • φ := by
    ext x; rfl
  rw [hlim] at H
  refine H.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  ext x
  simp [G, hε.1, hε.2.le]
  rfl

/-- Réduction de (iii) à `corol:convolTestFun`, appliqué à `ρ̄`. -/
private lemma cdE_tendsto_of_corol (T : 𝓓'ᵈ) (ρ φ : 𝓓ᵈ)
    (hc : Tendsto (fun ε => convolTest (noyauEpsTest (reflTest ρ) ε) φ) (𝓝[>] 0)
      (𝓝 ((∫ x, reflTest ρ x) • φ))) :
    Tendsto (fun ε => ∫ x, convolDistrib T (noyauEpsTest ρ ε) x * φ x) (𝓝[>] 0)
      (𝓝 ((∫ x, ρ x) * T φ)) := by
  have h1 : ∀ ε, reflTest (noyauEpsTest ρ ε) = noyauEpsTest (reflTest ρ) ε := fun ε => by
    ext y
    change noyauEps ρ ε (-y) = (ε ^ d)⁻¹ * ρ (-(ε⁻¹ • y))
    simp [noyauEps]
  have h2 : ∫ x, reflTest ρ x = ∫ x, ρ x := integral_neg_eq_self (fun x => ρ x) volume
  have hT : Continuous (fun ψ : 𝓓ᵈ => T ψ) := T.continuous
  have H := (hT.tendsto _).comp hc
  have e : T ((∫ x, ρ x) • φ) = (∫ x, ρ x) * T φ := by rw [map_smul, smul_eq_mul]
  rw [h2, e] at H
  refine H.congr fun ε => ?_
  simp only [Function.comp_apply, prop_convolDistrib_integral, h1]

/-- **Prop. `prop:convolDistrib` (iii).** `T ⋆ ρ_ε ⇀ (∫ ρ) T` au sens des distributions lorsque
`ε → 0⁺` : `⟨T ⋆ ρ_ε, φ⟩ → (∫ ρ) ⟨T, φ⟩` pour toute `φ`. Preuve : par l'identité,
`⟨T ⋆ ρ_ε, φ⟩ = ⟨T, ρ̄_ε ⋆ φ⟩`, et `ρ̄_ε ⋆ φ → (∫ ρ) φ` dans `𝓓` (`corol_convolTestFun`). -/
theorem prop_convolDistrib_tendsto (T : 𝓓'ᵈ) (ρ φ : 𝓓ᵈ) :
    Tendsto (fun ε => ∫ x, convolDistrib T (noyauEpsTest ρ ε) x * φ x) (𝓝[>] 0)
      (𝓝 ((∫ x, ρ x) * T φ)) :=
  cdE_tendsto_of_corol T ρ φ (corol_convolTestFun _ _)

/-- A test function on `ℝ^d` with unit integral (normalized bump). -/
private lemma cdE_exists_test_integral_one : ∃ ρ : 𝓓ᵈ, ∫ x, ρ x = 1 := by
  let χ : ContDiffBump (0 : ℝᵈ) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : 𝓓ᵈ :=
    { toFun := χ
      contDiff' := χ.contDiff
      hasCompactSupport' := χ.hasCompactSupport
      tsupport_subset' := by simp }
  have hpos : 0 < ∫ x, ψ x :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) χ.continuous
      χ.hasCompactSupport (fun x => χ.nonneg)
      (by change χ 0 ≠ 0; rw [χ.one_of_mem_closedBall (Metric.mem_closedBall_self χ.rIn_pos.le)]
          exact one_ne_zero)
  refine ⟨(∫ x, ψ x)⁻¹ • ψ, ?_⟩
  change ∫ x, (∫ x, ψ x)⁻¹ * ψ x = 1
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

/-- **Prop. `prop:convolDistrib` (iii), densité.** `C^∞(ℝ^d)` est dense dans `𝓓'(ℝ^d)` au sens
des distributions (convergence simple, par suites) : `f_n := T ⋆ ρ_{1/(n+1)}` avec `∫ ρ = 1`. -/
theorem prop_convolDistrib_dense (T : 𝓓'ᵈ) :
    ∃ f : ℕ → ℝᵈ → ℝ, (∀ n, ContDiff ℝ ∞ (f n)) ∧
      ∀ φ : 𝓓ᵈ, Tendsto (fun n => Distribution.ofFun ⊤ (f n) volume ⊤ φ) atTop (𝓝 (T φ)) := by
  obtain ⟨ρ, hρ⟩ := cdE_exists_test_integral_one (d := d)
  refine ⟨fun n => convolDistrib T (noyauEpsTest ρ (1 / ((n : ℝ) + 1))),
    fun n => prop_convolDistrib_contDiff T _, fun φ => ?_⟩
  have hs : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => by
        simp only [mem_Ioi]; positivity)
  have H := ((prop_convolDistrib_tendsto T ρ φ).comp hs)
  rw [hρ, one_mul] at H
  refine H.congr fun n => ?_
  simp only [Function.comp_apply, prop_convolDistrib_ofFun, prop_convolDistrib_integral]

end M1Analyse
