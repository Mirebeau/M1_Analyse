/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import M1Analyse.Compacite.Lax

/-!
# §3.5 Point fixe de Brouwer (`subsec:Brouwer`)

Source : `Include/Compacite.tex`, sous-section `subsec:Brouwer`.

Le théorème de point fixe de Brouwer (`th:Brouwer`) est absent de Mathlib. Le lemme de Lax
(`lem:chgVarLax`), démontré dans le cours pour `d = 2` seulement, est démontré en toute dimension
dans `M1Analyse/Compacite/Lax.lean` ; on en déduit `lem:noretractSmooth`, `corol:noretract` et
`th:Brouwer`.

On formalise :
* la formule de changement de variable `th:chgVarIntegr`, citée sans preuve par le cours, et
  présente dans Mathlib (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`) ;
* le cas `d = 1` du théorème de Brouwer, par le théorème des valeurs intermédiaires ;
* l'argument de rétraction du corollaire (non numéroté) suivant `th:Brouwer` : si une boule `B`
  a la propriété du point fixe et se rétracte sur `K`, alors `K` a la propriété du point fixe.
-/

open Set MeasureTheory

namespace M1Analyse

/-- **Thm. `th:chgVarIntegr` (Changement de variable dans une intégrale).** Soient
`U, V ⊆ ℝ^d` ouverts, `φ ∈ C¹(U, V)` un difféomorphisme, et `f : V → ℝ` intégrable. Alors
`∫_V f(x) dx = ∫_U f(φ(x)) |det J(x)| dx`, où `det J(x)` est le jacobien de `φ`
(déterminant de la différentielle `fderiv ℝ φ x`).
Remarque : l'énoncé Mathlib ne requiert que l'injectivité et la différentiabilité de `φ` sur
`U` ; les hypothèses de difféomorphisme (inverse `C¹`) et d'intégrabilité du cours sont gardées
pour la fidélité mais ne servent pas.
Preuve (absente du cours) : formule de Mathlib
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` (d'après Fremlin : sur des morceaux
où `φ ≈ A` linéaire, `|φ(B)| ≈ |det A| |B|`, par recouvrement de Besicovitch). -/
theorem th_chgVarIntegr {d : ℕ} (U V : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U)
    (_hV : IsOpen V) (φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hφ : ContDiffOn ℝ 1 φ U) (hinj : InjOn φ U) (himg : φ '' U = V)
    (_hinv : ContDiffOn ℝ 1 (Function.invFunOn φ U) V)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (_hf : IntegrableOn f V) :
    ∫ x in V, f x = ∫ x in U, f (φ x) * |(fderiv ℝ φ x).det| := by
  have hder : ∀ x ∈ U, HasFDerivWithinAt φ (fderiv ℝ φ x) U x := fun x hx =>
    (((hφ.differentiableOn one_ne_zero) x hx).differentiableAt
      (hU.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  subst himg
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hder hinj f]
  simp only [smul_eq_mul, mul_comm]

/-- **Cas `d = 1` du théorème de Brouwer** (`th:Brouwer`). Toute fonction continue
`f : [-1, 1] → [-1, 1]` admet un point fixe (la boule unité fermée de `ℝ` est `[-1, 1]`).
Preuve : théorème des valeurs intermédiaires appliqué à `x ↦ f(x) - x`. -/
theorem brouwer_dim_one (f : C(Icc (-1 : ℝ) 1, Icc (-1 : ℝ) 1)) : ∃ x, f x = x := by
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  set g : ℝ → ℝ := fun y => (f (projIcc (-1) 1 hab y) : ℝ) - y
  have hg : Continuous g := by
    have : Continuous fun y => (f (projIcc (-1) 1 hab y) : ℝ) :=
      continuous_subtype_val.comp (f.continuous.comp continuous_projIcc)
    exact this.sub continuous_id
  have h0 : (0 : ℝ) ∈ Icc (g 1) (g (-1)) := by
    constructor
    · have := (f (projIcc (-1) 1 hab 1)).2.2
      simp only [g]; linarith
    · have := (f (projIcc (-1) 1 hab (-1))).2.1
      simp only [g]; linarith
  obtain ⟨y, hy, hgy⟩ := intermediate_value_Icc' hab hg.continuousOn h0
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  have : projIcc (-1) 1 hab y = ⟨y, hy⟩ := projIcc_of_mem hab hy
  simp only [g, this] at hgy
  linarith

/-- Argument de rétraction (corollaire suivant `th:Brouwer`, premier point). Soit `K ⊆ B`, et
`P ∈ C⁰(B, K)` une rétraction (`P|_K = Id`). Si toute `g ∈ C⁰(B, B)` admet un point fixe, alors
toute `f ∈ C⁰(K, K)` admet un point fixe.
Remarque : le cours applique ceci avec `B` la boule unité de `ℝ^d`, l'hypothèse étant alors
fournie par `th:Brouwer` (`th_Brouwer`) ; voir `corol_Brouwer_convexe`. -/
theorem fixedPoint_of_retract {X : Type*} [TopologicalSpace X] {B K : Set X} (hKB : K ⊆ B)
    (hB : ∀ g : C(B, B), ∃ x, g x = x) (P : C(B, K)) (hP : ∀ x : K, P ⟨x, hKB x.2⟩ = x)
    (f : C(K, K)) : ∃ x, f x = x := by
  -- `x` point fixe de `f ∘ P` (vue dans `B`) ; alors `x ∈ K` et `P x = x`
  set ι : C(K, B) := ⟨fun x => ⟨x, hKB x.2⟩, by fun_prop⟩
  obtain ⟨x, hx⟩ := hB (ι.comp (f.comp P))
  have hxK : (x : X) ∈ K := by
    rw [← hx]; exact (f (P x)).2
  have hPx : P x = ⟨x, hxK⟩ := by
    have := hP ⟨x, hxK⟩
    simpa using this
  refine ⟨⟨x, hxK⟩, Subtype.ext ?_⟩
  have := congrArg Subtype.val hx
  simp only [ContinuousMap.comp_apply, hPx] at this
  exact this

section Lax

open Metric ContinuousLinearMap
open scoped Convolution

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- **Lem. `lem:chgVarLax` (Lax).** Soient `φ ∈ C^2(ℝ^d, ℝ^d)` telle que `φ(x) = x` pour tout
`x ∉ B` (`B` boule unité fermée), et `f ∈ 𝓓(ℝ^d)`. Alors `∫ f(x) dx = ∫ f(φ(x)) det J(x) dx`, où
`det J(x)` est le jacobien de `φ`, avec son signe.
Remarque : Mathlib ne contient que la formule pour `φ` injective (`th_chgVarIntegr`) ; d'abord
posé comme axiome à la demande de l'auteur, l'énoncé est maintenant démontré.
Preuve (celle du cours) : par homotopie `φ_t = Id + t(φ - Id)`,
la dérivée de `t ↦ ∫ f(φ_t) det Dφ_t` est l'intégrale d'une divergence (identité de Piola), donc
nulle (`lem_chgVarLax_proof`, `M1Analyse/Compacite/Lax.lean`). -/
theorem lem_chgVarLax {φ : ℝᵈ → ℝᵈ} (hφ : ContDiff ℝ 2 φ)
    (hφB : ∀ x, x ∉ closedBall (0 : ℝᵈ) 1 → φ x = x) {f : ℝᵈ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∫ x, f x = ∫ x, f (φ x) * (fderiv ℝ φ x).det :=
  lem_chgVarLax_proof hφ hφB hf hfc

/-- **Lem. `lem:noretractSmooth`.** Si `φ ∈ C^2(ℝ^d, ℝ^d)` et `φ(x) = x` pour tout `x ∉ B`, alors
`B ⊂ φ(B)`. Preuve : celle du cours (fonction plateau d'intégrale `1` dans une boule évitant
le compact `φ(B)`, et `lem:chgVarLax`). -/
theorem lem_noretractSmooth {φ : ℝᵈ → ℝᵈ} (hφ : ContDiff ℝ 2 φ)
    (hφB : ∀ x, x ∉ closedBall (0 : ℝᵈ) 1 → φ x = x) :
    closedBall (0 : ℝᵈ) 1 ⊆ φ '' closedBall 0 1 := by
  intro y₀ hy₀
  by_contra hnot
  have hK : IsClosed (φ '' closedBall (0 : ℝᵈ) 1) :=
    ((isCompact_closedBall 0 1).image hφ.continuous).isClosed
  -- un point `z` de la boule ouverte hors de `φ(B)`
  obtain ⟨z, hzU, hzB⟩ : ∃ z, z ∈ (φ '' closedBall (0 : ℝᵈ) 1)ᶜ ∧ z ∈ ball (0 : ℝᵈ) 1 := by
    have hcl : y₀ ∈ closure (ball (0 : ℝᵈ) 1) := by
      rwa [closure_ball (0 : ℝᵈ) one_ne_zero]
    exact mem_closure_iff.1 hcl _ hK.isOpen_compl hnot
  obtain ⟨ε, hε, hεsub⟩ : ∃ ε > 0, ball z ε ⊆ (φ '' closedBall (0 : ℝᵈ) 1)ᶜ ∩ ball 0 1 :=
    Metric.isOpen_iff.1 (hK.isOpen_compl.inter isOpen_ball) z ⟨hzU, hzB⟩
  let b : ContDiffBump z := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  set f : ℝᵈ → ℝ := b.normed volume with hf_def
  have hsupp : Function.support f = ball z ε := b.support_normed_eq
  have hzero : ∀ x, f (φ x) = 0 := by
    intro x
    by_contra hx
    have hmem : φ x ∈ ball z ε := hsupp ▸ hx
    by_cases hxB : x ∈ closedBall (0 : ℝᵈ) 1
    · exact (hεsub hmem).1 ⟨x, hxB, rfl⟩
    · rw [hφB x hxB] at hmem
      exact hxB (ball_subset_closedBall (hεsub hmem).2)
  have h1 : ∫ x, f x = 1 := b.integral_normed
  have h2 := lem_chgVarLax hφ hφB (f := f) b.contDiff_normed b.hasCompactSupport_normed
  simp only [hzero, zero_mul, integral_zero] at h2
  rw [h1] at h2
  exact one_ne_zero h2

/-- **Cor. `corol:noretract` (Non rétractation de la boule sur la sphère).** Si `φ ∈ C^0(B, B)`
et `φ(x) = x` pour tout `x ∈ ∂B`, alors `φ(B) = B`.
Preuve (variante du cours) : on régularise `(φ - Id) ∘ π` (`π` rétraction radiale sur `B`),
uniformément continue et nulle hors de `B`, ce qui évite un noyau radial centré ; on applique
`lem:noretractSmooth` à une version dilatée, et l'on conclut par fermeture de `φ(B)` au lieu
d'une extraction de sous-suite. -/
theorem corol_noretract {φ : ℝᵈ → ℝᵈ} (hφc : ContinuousOn φ (closedBall 0 1))
    (hφB : MapsTo φ (closedBall 0 1) (closedBall 0 1))
    (hφS : ∀ x ∈ sphere (0 : ℝᵈ) 1, φ x = x) :
    φ '' closedBall 0 1 = closedBall 0 1 := by
  refine Subset.antisymm hφB.image_subset ?_
  have hK : IsClosed (φ '' closedBall (0 : ℝᵈ) 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hφc).isClosed
  intro y hy
  rw [← hK.closure_eq, Metric.mem_closure_iff]
  intro δ hδ
  -- rétraction radiale `π` de `ℝᵈ` sur `B`, et `g := (φ - id) ∘ π`, nulle hors de `B`
  set π : ℝᵈ → ℝᵈ := fun x => (max 1 ‖x‖)⁻¹ • x with hπ_def
  have hπc : Continuous π := by
    have h : Continuous fun x : ℝᵈ => (max 1 ‖x‖)⁻¹ :=
      (continuous_const.max continuous_norm).inv₀ fun x => by positivity
    exact h.smul continuous_id
  have hπB : ∀ x, π x ∈ closedBall (0 : ℝᵈ) 1 := by
    intro x
    rw [mem_closedBall_zero_iff, hπ_def, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < max 1 ‖x‖)]
    rw [inv_mul_le_iff₀ (by positivity)]
    simp
  have hπid : ∀ x, ‖x‖ ≤ 1 → π x = x := by
    intro x hx
    simp [hπ_def, max_eq_left hx]
  have hπS : ∀ x, 1 < ‖x‖ → π x ∈ sphere (0 : ℝᵈ) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, hπ_def, norm_smul, max_eq_right hx.le, norm_inv, norm_norm,
      inv_mul_cancel₀ (by positivity)]
  set g : ℝᵈ → ℝᵈ := fun x => φ (π x) - π x with hg_def
  have hgc : Continuous g := (hφc.comp_continuous hπc hπB).sub hπc
  have hg0 : ∀ x, 1 < ‖x‖ → g x = 0 := by
    intro x hx
    simp [hg_def, hφS _ (hπS x hx)]
  have hgcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝᵈ) 1) fun x hx => hg0 x ?_
    simpa using hx
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuous_iff.1
    (hgcs.uniformContinuous_of_continuous hgc) (δ / 2) (half_pos hδ)
  -- régularisation de `g` par un noyau `C^∞` de rayon `r`
  set r : ℝ := min (η / 2) (δ / 4) with hr_def
  have hr : 0 < r := lt_min (half_pos hη) (by positivity)
  have hrη : r < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  have hrδ : r ≤ δ / 4 := min_le_right _ _
  let bump : ContDiffBump (0 : ℝᵈ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  set gr : ℝᵈ → ℝᵈ := bump.normed volume ⋆[lsmul ℝ ℝ, volume] g with hgr_def
  have hgr_smooth : ContDiff ℝ 2 gr :=
    bump.hasCompactSupport_normed.contDiff_convolution_left _ bump.contDiff_normed
      hgc.locallyIntegrable
  have hgr_close : ∀ x, dist (gr x) (g x) ≤ δ / 2 := fun x =>
    bump.dist_normed_convolution_le hgc.aestronglyMeasurable fun t ht =>
      (hηg (lt_trans (mem_ball.1 ht) hrη)).le
  have hgr0 : ∀ x, 1 + r < ‖x‖ → gr x = 0 := by
    intro x hx
    have hball : ∀ t ∈ ball x bump.rOut, g t = g x := by
      intro t ht
      have ht' : dist t x < r := ht
      have : 1 < ‖t‖ := by
        have := norm_sub_norm_le x t
        rw [← dist_eq_norm, dist_comm] at this
        linarith
      rw [hg0 t this, hg0 x (by linarith)]
    rw [hgr_def, bump.normed_convolution_eq_right hball, hg0 x (by linarith)]
  -- l'application lisse `ψ`, égale à l'identité hors de `B`
  set ψ : ℝᵈ → ℝᵈ := fun x => (1 + r)⁻¹ • ((1 + r) • x + gr ((1 + r) • x)) with hψ_def
  have hψ : ContDiff ℝ 2 ψ := by
    have h1 : ContDiff ℝ 2 fun x : ℝᵈ => (1 + r) • x := contDiff_id.const_smul _
    exact (h1.add (hgr_smooth.comp h1)).const_smul (1 + r)⁻¹
  have hψB : ∀ x, x ∉ closedBall (0 : ℝᵈ) 1 → ψ x = x := by
    intro x hx
    have hx1 : 1 < ‖x‖ := by simpa using hx
    have : 1 + r < ‖(1 + r) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith
    simp only [hψ_def, hgr0 _ this, add_zero, smul_smul,
      inv_mul_cancel₀ (by linarith : (1 + r) ≠ 0), one_smul]
  have hy' : (1 + r)⁻¹ • y ∈ closedBall (0 : ℝᵈ) 1 := by
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (by linarith),
      inv_mul_le_iff₀ (by linarith)]
    linarith
  obtain ⟨x, hx, hxy⟩ := lem_noretractSmooth hψ hψB hy'
  set z : ℝᵈ := (1 + r) • x with hz_def
  have hz : z + gr z = y := by
    have := congrArg (fun v => (1 + r) • v) hxy
    simpa only [hψ_def, smul_smul, mul_inv_cancel₀ (by linarith : (1 + r) ≠ 0), one_smul]
      using this
  have hzn : ‖z‖ ≤ 1 + r := by
    have hx1 : ‖x‖ ≤ 1 := by simpa using hx
    rw [hz_def, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
    nlinarith
  have hzπ : ‖z - π z‖ ≤ r := by
    by_cases h1 : ‖z‖ ≤ 1
    · rw [hπid z h1, sub_self, norm_zero]; exact hr.le
    · push Not at h1
      have : z - π z = (1 - ‖z‖⁻¹) • z := by
        simp only [hπ_def, max_eq_right h1.le, sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg, sub_mul,
        inv_mul_cancel₀ (by positivity)]
      · linarith
      · rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1.le
  refine ⟨φ (π z), ⟨π z, hπB z, rfl⟩, ?_⟩
  have hφπ : φ (π z) = g z + π z := by simp [hg_def]
  rw [hφπ, ← hz, dist_eq_norm]
  have : z + gr z - (g z + π z) = (gr z - g z) + (z - π z) := by abel
  rw [this]
  calc ‖(gr z - g z) + (z - π z)‖ ≤ ‖gr z - g z‖ + ‖z - π z‖ := norm_add_le _ _
    _ ≤ δ / 2 + δ / 4 := by
        gcongr
        · rw [← dist_eq_norm]; exact hgr_close z
        · exact hzπ.trans hrδ
    _ < δ := by linarith

/-- **Th. `th:Brouwer` (Point fixe de Brouwer).** Toute `f ∈ C^0(B, B)` admet un point fixe.
Preuve : celle du cours (rétraction `x ↦ x + λ(x)(x - f(x))` sur la sphère, contredisant
`corol:noretract`). -/
theorem th_Brouwer {f : ℝᵈ → ℝᵈ} (hfc : ContinuousOn f (closedBall 0 1))
    (hfB : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : ℝᵈ) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- coefficients du trinôme `P_x(λ) = a λ² + 2 b λ + c`
  set a : ℝᵈ → ℝ := fun x => ‖x - f x‖ ^ 2 with ha_def
  set b : ℝᵈ → ℝ := fun x => inner ℝ x (x - f x) with hb_def
  set c : ℝᵈ → ℝ := fun x => ‖x‖ ^ 2 - 1 with hc_def
  set lam : ℝᵈ → ℝ := fun x => (-b x + √(b x ^ 2 - a x * c x)) / a x with hlam_def
  set φ : ℝᵈ → ℝᵈ := fun x => x + lam x • (x - f x) with hφ_def
  have ha0 : ∀ x ∈ closedBall (0 : ℝᵈ) 1, a x ≠ 0 := by
    intro x hx
    have : x - f x ≠ 0 := sub_ne_zero.2 (hno x hx).symm
    simp only [ha_def]
    positivity
  have hc0 : ∀ x ∈ closedBall (0 : ℝᵈ) 1, c x ≤ 0 := by
    intro x hx
    have : ‖x‖ ≤ 1 := by simpa using hx
    simp only [hc_def]
    nlinarith [norm_nonneg x]
  have hcont : ContinuousOn φ (closedBall 0 1) := by
    have hfx : ContinuousOn (fun x => x - f x) (closedBall (0 : ℝᵈ) 1) :=
      continuousOn_id.sub hfc
    have hacont : ContinuousOn a (closedBall (0 : ℝᵈ) 1) := (hfx.norm).pow 2
    have hbcont : ContinuousOn b (closedBall (0 : ℝᵈ) 1) := continuousOn_id.inner hfx
    have hccont : ContinuousOn c (closedBall (0 : ℝᵈ) 1) :=
      (continuous_norm.pow 2).continuousOn.sub continuousOn_const
    have hlc : ContinuousOn lam (closedBall (0 : ℝᵈ) 1) :=
      (hbcont.neg.add ((hbcont.pow 2).sub (hacont.mul hccont)).sqrt).div hacont ha0
    exact continuousOn_id.add (hlc.smul hfx)
  have hnorm : ∀ x ∈ closedBall (0 : ℝᵈ) 1, ‖φ x‖ = 1 := by
    intro x hx
    have hD : 0 ≤ b x ^ 2 - a x * c x := by
      have : 0 ≤ a x := by simp only [ha_def]; positivity
      nlinarith [hc0 x hx, sq_nonneg (b x)]
    have hs := Real.sq_sqrt hD
    have hla : lam x * a x = -b x + √(b x ^ 2 - a x * c x) := by
      simp only [hlam_def]; field_simp [ha0 x hx]
    have hkey : a x * lam x ^ 2 + 2 * b x * lam x + c x = 0 := by
      have : a x * (a x * lam x ^ 2 + 2 * b x * lam x + c x) = 0 := by
        linear_combination (lam x * a x + b x + √(b x ^ 2 - a x * c x)) * hla + hs
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (ha0 x hx)
      · exact h
    have hsq : ‖φ x‖ ^ 2 = 1 := by
      simp only [hφ_def]
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      simp only [ha_def, hb_def, hc_def] at hkey
      linear_combination hkey
    have := norm_nonneg (φ x)
    nlinarith [sq_nonneg (‖φ x‖ - 1)]
  have hmaps : MapsTo φ (closedBall 0 1) (closedBall 0 1) := fun x hx => by
    simp [hnorm x hx]
  have hfix : ∀ x ∈ sphere (0 : ℝᵈ) 1, φ x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hxB : x ∈ closedBall (0 : ℝᵈ) 1 := sphere_subset_closedBall hx
    have hcx : c x = 0 := by simp [hc_def, hx1]
    have hbx : 0 ≤ b x := by
      have h1 : inner ℝ x (f x) ≤ 1 := by
        have h2 := real_inner_le_norm x (f x)
        have h3 : ‖f x‖ ≤ 1 := by simpa using hfB hxB
        rw [hx1] at h2
        linarith
      simp only [hb_def, inner_sub_right, real_inner_self_eq_norm_sq, hx1]
      linarith
    have : lam x = 0 := by
      simp only [hlam_def, hcx, mul_zero, sub_zero, Real.sqrt_sq hbx, neg_add_cancel, zero_div]
    simp [hφ_def, this]
  have himg := corol_noretract hcont hmaps hfix
  have h0 : (0 : ℝᵈ) ∈ φ '' closedBall 0 1 := by
    rw [himg]; simp
  obtain ⟨x, hx, hx0⟩ := h0
  have := hnorm x hx
  rw [hx0, norm_zero] at this
  exact zero_ne_one this

end Lax

end M1Analyse
