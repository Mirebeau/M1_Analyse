/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.ProdL2
import M1Analyse.Sobolev.ConvolutionSobolev
import M1Analyse.Sobolev.ConvolutionLp

/-!
# §5.2 Espaces de Sobolev `W^{1,p}(Ω)` et problème de Poisson (`subsec:convolSobolev`, suite)

Source : `Include/Sobolev.tex`, sous-section `subsec:convolSobolev`, de `def:Sobolev` à
`th:pbPoisson`.

Décision de l'auteur : seul le cas `s = 1` est formalisé. `W^{1,p}(Ω)` est le sous-espace
(fermé) `W1p Ω p` de `L^p(Ω) × L^p(Ω)^d` (`LpGrad`, `WithLp p` de Mathlib, de norme
`(‖f‖_p^p + ∑ᵢ ‖gᵢ‖_p^p)^{1/p}`) formé des couples `(f, ∇f)` ; ses éléments forment le type
`Sobolev1 Ω p`, avec `u.val = f` et `u.grad i = ∂ᵢ f` ; `H^1(Ω) = H1 Ω`,
`H^1_0(Ω) = H10 Ω`. `L^p(Ω)` est `Lp ℝ p (volume.restrict Ω)`.

`th:prolSobolev` (admis) n'est pas formalisé : sa conclusion définit la propriété
`ProlongementSobolev`, prise en hypothèse à la place de la régularité de `Ω` (`def:ouvertReg`,
non formalisée). `def:convolDistrib` et `prop:convolDistrib` : `Sobolev/ConvolDistrib.lean`.
-/

open MeasureTheory Set
open scoped ENNReal Distributions LineDeriv InnerProductSpace

namespace M1Analyse

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- Une fonction test est dans `L^q(Ω)` pour tout `q`. -/
private lemma w1p_memLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) (φ : 𝓓(Ω, ℝ)) :
    MemLp φ q (volume.restrict (Ω : Set ℝᵈ)) :=
  φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport

/-- `L^p(Ω) ⊆ L^1_loc(Ω)` pour `p ≥ 1`. -/
private lemma w1p_locInt {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) : LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)

private lemma w1p_ofFun_apply {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) (ψ : 𝓓(Ω, ℝ)) :
    Distribution.ofFun Ω (f : ℝᵈ → ℝ) volume ⊤ ψ = ∫ x in (Ω : Set ℝᵈ), f x * ψ x := by
  rw [Distribution.ofFun_apply (w1p_locInt f), setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp only [smul_eq_mul, mul_comm]
  · intro x hx
    simp [ψ.zero_on_compl hx]

private lemma w1p_ofFun_add {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f g : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) :
    Distribution.ofFun Ω ((f + g : Lp ℝ p _) : ℝᵈ → ℝ) volume ⊤ =
      Distribution.ofFun Ω (f : ℝᵈ → ℝ) volume ⊤ + Distribution.ofFun Ω (g : ℝᵈ → ℝ) volume ⊤ := by
  rw [Distribution.ofFun_congr_ae (Lp.coeFn_add f g),
    Distribution.ofFun_add (w1p_locInt f) (w1p_locInt g)]

private lemma w1p_ofFun_smul {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : ℝ) (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) :
    Distribution.ofFun Ω ((c • f : Lp ℝ p _) : ℝᵈ → ℝ) volume ⊤ =
      c • Distribution.ofFun Ω (f : ℝᵈ → ℝ) volume ⊤ := by
  rw [Distribution.ofFun_congr_ae (Lp.coeFn_smul c f), Distribution.ofFun_smul]

/-- Espace ambiant `L^p(Ω) × L^p(Ω)^d` de `W^{1,p}(Ω)`, muni de la norme
`‖(f, g)‖ = (‖f‖_p^p + ∑ᵢ ‖gᵢ‖_p^p)^{1/p}` (maximum des normes si `p = ∞`). -/
abbrev LpGrad (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  WithLp p (Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) ×
    PiLp p (fun _ : Fin d => Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))))

/-- L'injection linéaire `𝓓(Ω) → L^q(Ω)`. -/
private noncomputable def w1p_toLp (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    𝓓(Ω, ℝ) →ₗ[ℝ] Lp ℝ q (volume.restrict (Ω : Set ℝᵈ)) where
  toFun φ := (w1p_memLp Ω q φ).toLp φ
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    rfl
  map_smul' c φ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    rfl

private lemma w1p_toLp_coe (Ω : TopologicalSpace.Opens ℝᵈ) (q : ℝ≥0∞) [Fact (1 ≤ q)]
    (φ : 𝓓(Ω, ℝ)) : (w1p_toLp Ω q φ : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] φ :=
  MemLp.coeFn_toLp (w1p_memLp Ω q φ)

/-- Dérivée partielle `∂ᵢ : 𝓓(Ω) → 𝓓(Ω)`. -/
private noncomputable def w1p_partial (Ω : TopologicalSpace.Opens ℝᵈ) (i : Fin d) :
    𝓓(Ω, ℝ) →L[ℝ] 𝓓(Ω, ℝ) :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single i (1 : ℝ))

private lemma w1p_partial_apply (Ω : TopologicalSpace.Opens ℝᵈ) (i : Fin d) (φ : 𝓓(Ω, ℝ))
    (x : ℝᵈ) : w1p_partial Ω i φ x = fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
  rw [w1p_partial, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ le_top]

/-- **Déf. `def:Sobolev` (Espace de Sobolev), cas `s = 1`.** Pour `p ∈ [1, ∞]`, `W^{1,p}(Ω)` est
l'ensemble des couples `(f, g) ∈ L^p(Ω) × L^p(Ω)^d` tels que `∂ᵢ U_f = U_{gᵢ}` dans `𝓓'(Ω)` pour
tout `i` (dérivée au sens des distributions, `∂_{eᵢ}` de Mathlib), c'est-à-dire `gᵢ = ∂ᵢ f`.
Un élément de `W^{1,p}(Ω)` est donc représenté par le couple `(f, ∇f)` (\claudereport) : le
gradient faible est unique (`W1p_fst_injective`) et la norme est celle du cours (`norm_W1p`,
`norm_W1p_top`). -/
noncomputable def W1p (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (LpGrad Ω p) where
  carrier := {u | ∀ i : Fin d,
    ∂_{EuclideanSpace.single i (1 : ℝ)} (Distribution.ofFun Ω (u.fst : ℝᵈ → ℝ) volume ⊤) =
      Distribution.ofFun Ω (u.snd i : ℝᵈ → ℝ) volume ⊤}
  add_mem' {u v} hu hv i := by
    simp only [WithLp.add_fst, WithLp.add_snd, PiLp.add_apply] at hu hv ⊢
    rw [w1p_ofFun_add, w1p_ofFun_add, LineDeriv.lineDerivOp_add, hu i, hv i]
  zero_mem' i := by
    simp only [WithLp.zero_fst, WithLp.zero_snd, PiLp.zero_apply]
    rw [Distribution.ofFun_congr_ae (Lp.coeFn_zero _ _ _), Distribution.ofFun_zero]
    exact LineDeriv.lineDerivOp_zero (V := ℝᵈ) (E := 𝓓'(Ω, ℝ)) (F := 𝓓'(Ω, ℝ)) _
  smul_mem' c u hu i := by
    simp only [WithLp.smul_fst, WithLp.smul_snd, PiLp.smul_apply] at hu ⊢
    rw [w1p_ofFun_smul, w1p_ofFun_smul, LineDeriv.lineDerivOp_smul, hu i]

/-- Appartenance à `W^{1,p}(Ω)` : `∂ᵢ U_f = U_{gᵢ}` pour tout `i`. -/
theorem mem_W1p {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : LpGrad Ω p} :
    u ∈ W1p Ω p ↔ ∀ i : Fin d,
      ∂_{EuclideanSpace.single i (1 : ℝ)} (Distribution.ofFun Ω (u.fst : ℝᵈ → ℝ) volume ⊤) =
        Distribution.ofFun Ω (u.snd i : ℝᵈ → ℝ) volume ⊤ :=
  Iff.rfl

/-- Type des éléments de `W^{1,p}(Ω)` (`def:Sobolev`, `s = 1`) : couples `(f, ∇f)`. -/
abbrev Sobolev1 (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Type := W1p Ω p

namespace Sobolev1

/-- La fonction `u ∈ L^p(Ω)`. -/
noncomputable def val {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) :=
  u.1.fst

/-- La dérivée faible `∂ᵢ u ∈ L^p(Ω)`. -/
noncomputable def grad {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) (i : Fin d) : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) :=
  u.1.snd i

/-- Le gradient faible `∇u ∈ L^p(Ω)^d`. -/
noncomputable def gradL {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) : PiLp p (fun _ : Fin d => Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) :=
  u.1.snd

theorem val_def {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) : u.val = (u : LpGrad Ω p).fst :=
  rfl

theorem grad_def {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) (i : Fin d) : u.grad i = (u : LpGrad Ω p).snd i :=
  rfl

theorem gradL_def {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) : u.gradL = (u : LpGrad Ω p).snd :=
  rfl

theorem gradL_apply {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev1 Ω p) (i : Fin d) : u.gradL i = u.grad i :=
  rfl

end Sobolev1

/-- Norme de `def:Sobolev` (`p < ∞`) : `‖u‖^p = ‖f‖_p^p + ∑ᵢ ‖∂ᵢ f‖_p^p`. -/
theorem norm_W1p {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Sobolev1 Ω p) :
    ‖u‖ ^ p.toReal = ‖u.val‖ ^ p.toReal + ∑ i, ‖u.grad i‖ ^ p.toReal := by
  have hp0 : 0 < p.toReal :=
    ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  have hu : ‖u‖ = ‖(u : LpGrad Ω p)‖ := rfl
  rw [hu, WithLp.prod_norm_eq_add hp0, PiLp.norm_eq_sum hp0, one_div,
    Real.rpow_inv_rpow (by positivity) hp0.ne', Real.rpow_inv_rpow (by positivity) hp0.ne']
  rfl

/-- Norme de `def:Sobolev` (`p = ∞`) : `‖u‖ = max(‖f‖_∞, maxᵢ ‖∂ᵢ f‖_∞)`. -/
theorem norm_W1p_top {Ω : TopologicalSpace.Opens ℝᵈ} (u : Sobolev1 Ω ∞) :
    ‖u‖ = max ‖u.val‖ (⨆ i, ‖u.grad i‖) := by
  have hu : ‖u‖ = ‖(u : LpGrad Ω ∞)‖ := rfl
  rw [hu, WithLp.prod_norm_eq_sup, PiLp.norm_eq_ciSup]
  rfl

/-- Unicité du gradient faible : `(f, ∇f) ↦ f` est injective sur `W^{1,p}(Ω)`, qui s'identifie
donc (isométriquement, pour la norme du cours) à un sous-espace de `L^p(Ω)`. -/
theorem W1p_fst_injective (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Injective fun u : Sobolev1 Ω p => u.val := by
  intro u v h
  simp only [Sobolev1.val_def] at h
  refine Subtype.ext (WithLp.ofLp_injective p (Prod.ext h (PiLp.ext fun i => Lp.ext ?_)))
  refine prop_distribL1Loc_injective Ω (w1p_locInt _) (w1p_locInt _) ?_
  have hu := mem_W1p.mp u.2 i
  have hv := mem_W1p.mp v.2 i
  rw [h] at hu
  exact hu.symm.trans hv

/-- Caractérisation faible : `u ∈ W^{1,p}(Ω)` ssi `∫ u ∂ᵢψ + ∫ gᵢ ψ = 0` pour toute `ψ`. -/
private lemma w1p_mem_iff {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : LpGrad Ω p) : u ∈ W1p Ω p ↔ ∀ (i : Fin d) (ψ : 𝓓(Ω, ℝ)),
      (∫ x in (Ω : Set ℝᵈ), u.fst x * w1p_partial Ω i ψ x) +
        ∫ x in (Ω : Set ℝᵈ), u.snd i x * ψ x = 0 := by
  refine forall_congr' fun i => ?_
  rw [DFunLike.ext_iff]
  refine forall_congr' fun ψ => ?_
  rw [Distribution.lineDerivOp_eq_lineDerivCLM, Distribution.lineDerivCLM_apply,
    w1p_ofFun_apply, w1p_ofFun_apply, neg_eq_iff_add_eq_zero]
  rfl

/-- Pairing `f ↦ ∫_Ω f ψ` continu sur `L^p(Ω)`, pour `ψ` fonction test. -/
private lemma w1p_continuous_pairing (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (ψ : 𝓓(Ω, ℝ)) :
    Continuous fun f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) =>
      ∫ x in (Ω : Set ℝᵈ), f x * ψ x := by
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have h : ∀ f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)),
      ∫ x in (Ω : Set ℝᵈ), f x * ψ x =
        ((ContinuousLinearMap.mul ℝ ℝ).lpPairing (volume.restrict (Ω : Set ℝᵈ)) p
          p.conjExponent).flip (w1p_toLp Ω p.conjExponent ψ) f := by
    intro f
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lpPairing_eq_integral]
    refine integral_congr_ae ((w1p_toLp_coe Ω p.conjExponent ψ).mono fun x hx => ?_)
    simp [hx]
  simp_rw [h]
  exact ContinuousLinearMap.continuous _

/-- **Prop. `prop:SobolevBanach`, `s = 1`.** `W^{1,p}(Ω)` est fermé dans `L^p(Ω) × L^p(Ω)^d`,
donc complet (instance `CompleteSpace`) : c'est un espace de Banach.
Preuve (différente du cours) : chaque relation `∫ f ∂ᵢψ + ∫ gᵢ ψ = 0` (`ψ ∈ 𝓓(Ω)`) est
l'annulation d'une forme linéaire continue (Hölder) ; `W^{1,p}(Ω)` est une intersection de
noyaux, sans passer par les suites de Cauchy ni la continuité de la dérivation dans `𝓓'(Ω)`. -/
theorem prop_SobolevBanach_isClosed (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : IsClosed (W1p Ω p : Set (LpGrad Ω p)) := by
  have h : (W1p Ω p : Set (LpGrad Ω p)) = ⋂ (i : Fin d) (ψ : 𝓓(Ω, ℝ)),
      (fun u : LpGrad Ω p => (∫ x in (Ω : Set ℝᵈ), u.fst x * w1p_partial Ω i ψ x) +
        ∫ x in (Ω : Set ℝᵈ), u.snd i x * ψ x) ⁻¹' {0} := by
    ext u
    simp only [SetLike.mem_coe, w1p_mem_iff, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun ψ => IsClosed.preimage ?_ isClosed_singleton
  exact ((w1p_continuous_pairing Ω p _).comp (WithLp.continuous_fst p _ _)).add
    ((w1p_continuous_pairing Ω p ψ).comp
      ((PiLp.continuous_apply p _ i).comp (WithLp.continuous_snd p _ _)))

instance (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (W1p Ω p) :=
  (prop_SobolevBanach_isClosed Ω p).completeSpace_coe


/-- Produit scalaire de `L²(Ω) × L²(Ω)^d`. -/
private lemma w1p_inner (Ω : TopologicalSpace.Opens ℝᵈ) (u v : LpGrad Ω 2) :
    ⟪u, v⟫_ℝ = (∫ x in (Ω : Set ℝᵈ), u.fst x * v.fst x) +
      ∑ i, ∫ x in (Ω : Set ℝᵈ), u.snd i x * v.snd i x := by
  simp only [WithLp.prod_inner_apply, PiLp.inner_apply, L2.inner_def, Real.inner_apply]
  rfl

/-- Espace de Sobolev `H^1(Ω) := W^{1,2}(Ω)` (`prop:SobolevBanach`), espace de Hilbert. -/
abbrev H1 (Ω : TopologicalSpace.Opens ℝᵈ) : Type := Sobolev1 Ω 2

/-- **Prop. `prop:SobolevBanach`, `p = 2`.** `H^1(Ω)` est un espace de Hilbert (structure héritée
de `L^2(Ω) × L^2(Ω)^d`), de produit scalaire `⟪u, v⟫ = ∫_Ω u v + ∑ᵢ ∫_Ω ∂ᵢu ∂ᵢv`. -/
theorem prop_SobolevBanach_inner (Ω : TopologicalSpace.Opens ℝᵈ) (u v : H1 Ω) :
    ⟪u, v⟫_ℝ = (∫ x in (Ω : Set ℝᵈ), u.val x * v.val x) +
      ∑ i, ∫ x in (Ω : Set ℝᵈ), u.grad i x * v.grad i x :=
  w1p_inner Ω (u : LpGrad Ω 2) v

/-- Fonction test vue dans `L^p(Ω) × L^p(Ω)^d` : `φ ↦ (φ, ∇φ)`. -/
noncomputable def testGrad (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓓(Ω, ℝ) →ₗ[ℝ] LpGrad Ω p :=
  (WithLp.linearEquiv p ℝ _).symm.toLinearMap ∘ₗ LinearMap.prod (w1p_toLp Ω p)
    ((WithLp.linearEquiv p ℝ _).symm.toLinearMap ∘ₗ
      LinearMap.pi fun i => w1p_toLp Ω p ∘ₗ (w1p_partial Ω i).toLinearMap)

theorem testGrad_fst (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓓(Ω, ℝ)) :
    ((testGrad Ω p φ).fst : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] φ :=
  w1p_toLp_coe Ω p φ

theorem testGrad_snd (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓓(Ω, ℝ))
    (i : Fin d) :
    ((testGrad Ω p φ).snd i : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)]
      fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
  (w1p_toLp_coe Ω p (w1p_partial Ω i φ)).trans
    (Filter.Eventually.of_forall (w1p_partial_apply Ω i φ))

/-- **Rem. `rem:bcDirichlet` (Conditions au bord de Dirichlet).** `W^{1,p}_0(Ω)` est l'adhérence
de `𝓓(Ω)`, plongé par `φ ↦ (φ, ∇φ)`. C'est un sous-espace fermé (`rem_bcDirichlet_isClosed`),
donc complet, de `W^{1,p}(Ω)` (`rem_bcDirichlet`), et séparable (`rem_bcDirichlet_separable`,
`Sobolev/W1p0Separable.lean`). -/
noncomputable def W1p0 (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (LpGrad Ω p) :=
  (LinearMap.range (testGrad Ω p)).topologicalClosure

/-- Intégration par parties pour deux fonctions test : `∫ φ ∂ᵢψ + ∫ ∂ᵢφ ψ = 0`. -/
private lemma w1p_ibp (Ω : TopologicalSpace.Opens ℝᵈ) (i : Fin d) (φ ψ : 𝓓(Ω, ℝ)) :
    (∫ x in (Ω : Set ℝᵈ), φ x * w1p_partial Ω i ψ x) +
      ∫ x in (Ω : Set ℝᵈ), w1p_partial Ω i φ x * ψ x = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [φ.zero_on_compl hx]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [ψ.zero_on_compl hx])]
  have h1 : Integrable (fun x => w1p_partial Ω i φ x * ψ x) :=
    ((w1p_partial Ω i φ).continuous.mul ψ.continuous).integrable_of_hasCompactSupport
      ψ.hasCompactSupport.mul_left
  have h2 : Integrable (fun x => φ x * w1p_partial Ω i ψ x) :=
    (φ.continuous.mul (w1p_partial Ω i ψ).continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.mul_right
  have h3 : Integrable (fun x => φ x * ψ x) :=
    (φ.continuous.mul ψ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right
  simp only [w1p_partial_apply] at h1 h2 ⊢
  rw [integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => (φ.contDiff.differentiable (by simp)) x)
    (fun x _ => (ψ.contDiff.differentiable (by simp)) x), neg_add_cancel]

/-- **Rem. `rem:bcDirichlet`.** `W^{1,p}_0(Ω) ⊆ W^{1,p}(Ω)` (intégration par parties pour les
fonctions test, et fermeture de `W^{1,p}(Ω)`). -/
theorem rem_bcDirichlet (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    W1p0 Ω p ≤ W1p Ω p := by
  refine Submodule.topologicalClosure_minimal _ ?_ (prop_SobolevBanach_isClosed Ω p)
  rintro _ ⟨φ, rfl⟩
  rw [w1p_mem_iff]
  intro i ψ
  have h1 : ∫ x in (Ω : Set ℝᵈ), (testGrad Ω p φ).fst x * w1p_partial Ω i ψ x =
      ∫ x in (Ω : Set ℝᵈ), φ x * w1p_partial Ω i ψ x :=
    integral_congr_ae ((testGrad_fst Ω p φ).mono fun x hx => by simp only [hx])
  have h2 : ∫ x in (Ω : Set ℝᵈ), (testGrad Ω p φ).snd i x * ψ x =
      ∫ x in (Ω : Set ℝᵈ), w1p_partial Ω i φ x * ψ x :=
    integral_congr_ae ((testGrad_snd Ω p φ i).mono fun x hx => by
      simp only [hx, w1p_partial_apply])
  rw [h1, h2]
  exact w1p_ibp Ω i φ ψ

/-- **Rem. `rem:bcDirichlet`.** `W^{1,p}_0(Ω)` est fermé, donc complet. -/
theorem rem_bcDirichlet_isClosed (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    IsClosed (W1p0 Ω p : Set (LpGrad Ω p)) :=
  Submodule.isClosed_topologicalClosure _

instance (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    CompleteSpace (W1p0 Ω p) :=
  (rem_bcDirichlet_isClosed Ω p).completeSpace_coe

/-- `H^1_0(Ω) := W^{1,2}_0(Ω)` (`rem:bcDirichlet`). -/
abbrev H10 (Ω : TopologicalSpace.Opens ℝᵈ) : Type := W1p0 Ω 2

namespace H10

/-- La fonction `u ∈ L^2(Ω)`. -/
noncomputable def val {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) :
    Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)) :=
  u.1.fst

/-- La dérivée faible `∂ᵢ u ∈ L^2(Ω)`. -/
noncomputable def grad {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) (i : Fin d) :
    Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ)) :=
  u.1.snd i

/-- Le gradient faible `∇u ∈ L^2(Ω)^d`. -/
noncomputable def gradL {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) :
    PiLp 2 (fun _ : Fin d => Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :=
  u.1.snd

theorem val_def {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) : u.val = (u : LpGrad Ω 2).fst :=
  rfl

theorem grad_def {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) (i : Fin d) :
    u.grad i = (u : LpGrad Ω 2).snd i :=
  rfl

theorem gradL_def {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) : u.gradL = (u : LpGrad Ω 2).snd :=
  rfl

theorem gradL_apply {Ω : TopologicalSpace.Opens ℝᵈ} (u : H10 Ω) (i : Fin d) :
    u.gradL i = u.grad i :=
  rfl

end H10

private lemma w1p_integrable_mul {Ω : TopologicalSpace.Opens ℝᵈ}
    (f g : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    Integrable (fun x => f x * g x) (volume.restrict (Ω : Set ℝᵈ)) := by
  simpa only [Real.inner_apply] using L2.integrable_inner (𝕜 := ℝ) f g

/-- La forme bilinéaire `Q(u, v) = ∫ (∇u · ∇v + u v)` est le produit scalaire. -/
private lemma w1p_integral_eq_inner (Ω : TopologicalSpace.Opens ℝᵈ) (u v : LpGrad Ω 2) :
    ∫ x in (Ω : Set ℝᵈ), ((∑ i, u.snd i x * v.snd i x) + u.fst x * v.fst x) = ⟪u, v⟫_ℝ := by
  rw [w1p_inner, integral_add (integrable_finsetSum _ fun i _ => w1p_integrable_mul _ _)
    (w1p_integrable_mul _ _), integral_finsetSum _ fun i _ => w1p_integrable_mul _ _, add_comm]

/-- Problème variationnel `Q(u, v) = ∫ f v` sur un sous-espace complet de `L² × (L²)^d`
(Lax–Milgram symétrique, i.e. représentation de Riesz). -/
private lemma w1p_poisson (Ω : TopologicalSpace.Opens ℝᵈ) (K : Submodule ℝ (LpGrad Ω 2))
    [CompleteSpace K] (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∃! u : K, ∀ v : K,
      ∫ x in (Ω : Set ℝᵈ), ((∑ i, (u : LpGrad Ω 2).snd i x * (v : LpGrad Ω 2).snd i x) +
          (u : LpGrad Ω 2).fst x * (v : LpGrad Ω 2).fst x) =
        ∫ x in (Ω : Set ℝᵈ), f x * (v : LpGrad Ω 2).fst x := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : StrongDual ℝ K,
      ∀ v : K, ℓ v = ∫ x in (Ω : Set ℝᵈ), f x * (v : LpGrad Ω 2).fst x := by
    refine ⟨innerSL ℝ f ∘L WithLp.fstL 2 ℝ _ _ ∘L K.subtypeL, fun v => ?_⟩
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def,
      Real.inner_apply]
    rfl
  have key : ∀ u : K, (∀ v : K,
      ∫ x in (Ω : Set ℝᵈ), ((∑ i, (u : LpGrad Ω 2).snd i x * (v : LpGrad Ω 2).snd i x) +
          (u : LpGrad Ω 2).fst x * (v : LpGrad Ω 2).fst x) =
        ∫ x in (Ω : Set ℝᵈ), f x * (v : LpGrad Ω 2).fst x) ↔
      InnerProductSpace.toDual ℝ K u = ℓ := by
    intro u
    rw [ContinuousLinearMap.ext_iff]
    refine forall_congr' fun v => ?_
    have h1 := w1p_integral_eq_inner Ω (u : LpGrad Ω 2) (v : LpGrad Ω 2)
    have h2 := hℓ v
    have h3 : InnerProductSpace.toDual ℝ K u v = ⟪(u : LpGrad Ω 2), (v : LpGrad Ω 2)⟫_ℝ := rfl
    rw [h3, h2, h1]
  refine ⟨(InnerProductSpace.toDual ℝ K).symm ℓ, (key _).mpr (by simp), fun u hu => ?_⟩
  rw [← (key u).mp hu, LinearIsometryEquiv.symm_apply_apply]

/-- **Th. `th:pbPoisson` (Problème de Poisson), problème de Neumann.** Pour `f ∈ L^2(Ω)`, il
existe une unique `u ∈ H^1(Ω)` telle que `Q(u, v) = L(v)` pour toute `v ∈ H^1(Ω)`, où
`Q(u, v) = ∫_Ω ⟨∇u, ∇v⟩ + u v` et `L(v) = ∫_Ω f v`.
Remarque : l'hypothèse « `Ω` borné » du cours est inutile et a été retirée (\claudereport).
Preuve : `Q` est exactement le produit scalaire de `H^1(Ω)` et `L` est continue ; théorème de
représentation de Riesz. -/
theorem th_pbPoisson_Neumann (Ω : TopologicalSpace.Opens ℝᵈ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∃! u : H1 Ω, ∀ v : H1 Ω,
      ∫ x in (Ω : Set ℝᵈ), ((∑ i, u.grad i x * v.grad i x) + u.val x * v.val x) =
        ∫ x in (Ω : Set ℝᵈ), f x * v.val x :=
  w1p_poisson Ω (W1p Ω 2) f

/-- **Th. `th:pbPoisson` (Problème de Poisson), problème de Dirichlet.** Pour `f ∈ L^2(Ω)`, il
existe une unique `u ∈ H^1_0(Ω)` telle que `Q(u, v) = L(v)` pour toute `v ∈ H^1_0(Ω)`.
Remarque : l'hypothèse « `Ω` borné » du cours est inutile et a été retirée (\claudereport).
Preuve : `Q` est le produit scalaire de `H^1_0(Ω)`, sous-espace fermé donc complet ; Riesz. -/
theorem th_pbPoisson_Dirichlet (Ω : TopologicalSpace.Opens ℝᵈ)
    (f : Lp ℝ 2 (volume.restrict (Ω : Set ℝᵈ))) :
    ∃! u : H10 Ω, ∀ v : H10 Ω,
      ∫ x in (Ω : Set ℝᵈ), ((∑ i, u.grad i x * v.grad i x) + u.val x * v.val x) =
        ∫ x in (Ω : Set ℝᵈ), f x * v.val x :=
  w1p_poisson Ω (W1p0 Ω 2) f

/-- Propriété de prolongement de Sobolev de `Ω`, pour l'exposant `p` : conclusion de
`th:prolSobolev` (admis dans le cours, non formalisé), cas `s = 1`. Il existe un opérateur
linéaire continu `P : W^{1,p}(Ω) → W^{1,p}(ℝ^d)` tel que `(P u)|_Ω = u`. Elle remplace
l'hypothèse « `Ω` régulier » (`corol_testDenseWspO`). -/
def ProlongementSobolev (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : Prop :=
  ∃ P : Sobolev1 Ω p →L[ℝ] Sobolev1 (⊤ : TopologicalSpace.Opens ℝᵈ) p, ∀ u : Sobolev1 Ω p,
    ((P u).val : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] u.val

open Filter Topology Metric
open scoped Convolution NNReal
open ContinuousLinearMap (lsmul)

/-! ### Lemmes auxiliaires : approximation par convolution, troncature -/

/-- Variante de `lem_convolTranslat` pour un noyau `f` intégrable de signe quelconque,
d'intégrale unité : `‖f ⋆ g - g‖_p^p ≤ ‖f‖_1^{p-1} ∫ |f(h)| ‖τ_h g - g‖_p^p dh`. -/
private lemma w1pDens_convolTranslat {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f g : ℝᵈ → ℝ}
    (hf : Integrable f) (hf1 : ∫ x, f x = 1) (hg : MemLp g p) :
    eLpNorm (f ⋆ g - g) p ^ p.toReal ≤ (∫⁻ h, ‖f h‖ₑ) ^ (p.toReal - 1) *
      ∫⁻ h, ‖f h‖ₑ * eLpNorm (fun x => g (x - h) - g x) p ^ p.toReal := by
  set r := p.toReal with hr_def
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hr : 1 ≤ r := by
    rw [hr_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hgm := hg.aestronglyMeasurable
  have hfg : AEStronglyMeasurable (f ⋆ g) volume :=
    hf.aestronglyMeasurable.convolution (lsmul ℝ ℝ) hgm
  have hτ : ∀ h, AEStronglyMeasurable (fun x => g (x - h) - g x) volume := fun h =>
    (hgm.comp_measurePreserving (measurePreserving_sub_right volume h)).sub hgm
  have hL : eLpNorm (f ⋆ g - g) p ^ r = ∫⁻ x, ‖(f ⋆ g) x - g x‖ₑ ^ r := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hfg.sub hgm), ← hr_def,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
    rfl
  have hR : ∀ h, eLpNorm (fun x => g (x - h) - g x) p ^ r =
      ∫⁻ x, ‖g (x - h) - g x‖ₑ ^ r := by
    intro h
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hτ h), ← hr_def,
      ← ENNReal.rpow_mul, one_div_mul_cancel hr0.ne', ENNReal.rpow_one]
  simp_rw [hL, hR]
  set A := ∫⁻ h, ‖f h‖ₑ with hA_def
  have hAt : A ^ (r - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) hf.hasFiniteIntegral.ne
  have hpt_bound : ∀ᵐ x, ‖(f ⋆ g) x - g x‖ₑ ^ r ≤
      A ^ (r - 1) * ∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ ^ r := by
    filter_upwards [(prop_convolLp hp hf hg).1] with x hx
    have hint : Integrable (fun h => f h * g (x - h)) := by
      simpa [ConvolutionExistsAt] using hx
    have heq : (f ⋆ g) x - g x = ∫ h, f h * (g (x - h) - g x) := by
      rw [convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, mul_sub]
      rw [integral_sub hint (hf.mul_const _), integral_mul_const, hf1, one_mul]
    have h1 : ‖(f ⋆ g) x - g x‖ₑ ≤ ∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ := by
      rw [heq]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp [enorm_mul]
    calc ‖(f ⋆ g) x - g x‖ₑ ^ r
        ≤ (∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ) ^ r := by gcongr
      _ ≤ A ^ (r - 1) * ∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ ^ r :=
          lintegral_mul_rpow_le volume hr hf.aestronglyMeasurable.enorm
            ((hgm.comp_measurePreserving (Measure.measurePreserving_sub_left volume x)).sub
              aestronglyMeasurable_const).enorm
  have hK : AEMeasurable (fun z : ℝᵈ × ℝᵈ => ‖f z.2‖ₑ * ‖g (z.1 - z.2) - g z.1‖ₑ ^ r)
      (volume.prod volume) :=
    hf.aestronglyMeasurable.enorm.comp_snd.mul
      (((hgm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant
        volume volume)).sub hgm.aemeasurable.comp_fst.aestronglyMeasurable).enorm.pow_const r)
  calc ∫⁻ x, ‖(f ⋆ g) x - g x‖ₑ ^ r
      ≤ ∫⁻ x, A ^ (r - 1) * ∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ ^ r :=
        lintegral_mono_ae hpt_bound
    _ = A ^ (r - 1) * ∫⁻ x, ∫⁻ h, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ ^ r :=
        lintegral_const_mul' _ _ hAt
    _ = A ^ (r - 1) * ∫⁻ h, ∫⁻ x, ‖f h‖ₑ * ‖g (x - h) - g x‖ₑ ^ r := by
        rw [lintegral_lintegral_swap hK]
    _ = A ^ (r - 1) * ∫⁻ h, ‖f h‖ₑ * ∫⁻ x, ‖g (x - h) - g x‖ₑ ^ r := by
        congr 1
        refine lintegral_congr fun h => ?_
        exact lintegral_const_mul'' _ ((hτ h).enorm.pow_const r)

/-- Estimation `‖ρ_ε ⋆ f - f‖_p ≤ ‖ρ‖_1 ω_p(εR)` pour un noyau `ρ` intégrable de signe
quelconque, supporté dans `B'(0, R)` et d'intégrale unité. -/
private lemma w1pDens_convolApprox_le {ρ : ℝᵈ → ℝ} (hρ : Integrable ρ) {R : ℝ}
    (hρs : Function.support ρ ⊆ closedBall 0 R) (hρ1 : ∫ x, ρ x = 1) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {f : ℝᵈ → ℝ} (hf : MemLp f p) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (noyauEps ρ ε ⋆ f - f) p ≤
      ENNReal.ofReal (∫ x, |ρ x|) * moduleTransl p f (ε * R) := by
  set r := p.toReal with hr_def
  have hr : 1 ≤ r := by
    rw [hr_def, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hpt hp
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hint := integrable_noyauEps hρ hε
  have H := w1pDens_convolTranslat hp hpt hint ((integral_noyauEps hε).trans hρ1) hf
  have hA : ∫⁻ h, ‖noyauEps ρ ε h‖ₑ = ENNReal.ofReal (∫ x, |ρ x|) := by
    have e : ∀ h, ‖noyauEps ρ ε h‖ₑ = ENNReal.ofReal (noyauEps (fun x => |ρ x|) ε h) := by
      intro h
      rw [← ofReal_norm, Real.norm_eq_abs]
      congr 1
      simp only [noyauEps, abs_mul, abs_inv, abs_pow, abs_of_pos hε]
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_noyauEps hρ.abs hε)
      (ae_of_all _ fun h => noyauEps_nonneg (fun x => abs_nonneg (ρ x)) hε h),
      integral_noyauEps hε]
  set A := ENNReal.ofReal (∫ x, |ρ x|) with hA_def
  set ω := moduleTransl p f (ε * R) with hω
  have H2 : ∫⁻ h, ‖noyauEps ρ ε h‖ₑ * eLpNorm (fun x => f (x - h) - f x) p ^ r ≤
      ∫⁻ h, ‖noyauEps ρ ε h‖ₑ * ω ^ r := by
    refine lintegral_mono fun h => ?_
    by_cases hh : noyauEps ρ ε h = 0
    · simp [hh]
    · gcongr
      have he : eLpNorm (fun x => f (x - h) - f x) p volume =
          eLpNorm (fun x => f x - f (x - h)) p volume := by
        rw [← eLpNorm_neg]
        congr 1
        funext x
        simp
      rw [he]
      have hn : ‖h‖ ≤ ε * R := by
        have h1 : ρ (ε⁻¹ • h) ≠ 0 := fun h' => hh (by simp [noyauEps, h'])
        have h2 := hρs h1
        rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le),
          inv_mul_le_iff₀ hε] at h2
        exact h2
      exact le_iSup₂ (f := fun h (_ : h ∈ closedBall (0 : ℝᵈ) (ε * R)) =>
        eLpNorm (fun x => f x - f (x - h)) p volume) h (mem_closedBall_zero_iff.2 hn)
  rw [lintegral_mul_const'' _ hint.aestronglyMeasurable.enorm, hA] at H2
  rw [hA] at H
  have hAr : A ^ (r - 1) * A = A ^ r := by
    have e : r = (r - 1) + 1 := by ring
    calc A ^ (r - 1) * A = A ^ (r - 1) * A ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = A ^ ((r - 1) + 1) := (ENNReal.rpow_add_of_nonneg _ _ (by linarith) zero_le_one).symm
      _ = A ^ r := by rw [← e]
  have key : eLpNorm (noyauEps ρ ε ⋆ f - f) p ^ r ≤ (A * ω) ^ r := by
    have h3 := H.trans (mul_le_mul_right H2 (A ^ (r - 1)))
    rwa [← mul_assoc, hAr, ← ENNReal.mul_rpow_of_nonneg _ _ hr0.le] at h3
  exact (ENNReal.rpow_le_rpow_iff hr0).1 key

/-- Convergence `ρ_ε ⋆ f → f` dans `L^p` (`p < ∞`) pour `ρ` continue à support compact,
d'intégrale unité, de signe quelconque. -/
private lemma w1pDens_tendsto_convol {ρ : ℝᵈ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρ1 : ∫ x, ρ x = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {f : ℝᵈ → ℝ}
    (hf : MemLp f p) :
    Tendsto (fun ε => eLpNorm (noyauEps ρ ε ⋆ f - f) p) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨R, hR⟩ := hρc.isCompact.isBounded.subset_closedBall (0 : ℝᵈ)
  set R' := max R 1 with hR'
  have hR'0 : 0 < R' := lt_max_of_lt_right one_pos
  have hs : Function.support ρ ⊆ closedBall 0 R' :=
    (subset_tsupport ρ).trans (hR.trans (closedBall_subset_closedBall (le_max_left _ _)))
  have hint : Integrable ρ := hρ.integrable_of_hasCompactSupport hρc
  have h1 : Tendsto (fun ε : ℝ => ε * R') (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun ε : ℝ => ε * R') (𝓝 0) (𝓝 (0 * R')) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos hε hR'0
  have hlim : Tendsto (fun ε => ENNReal.ofReal (∫ x, |ρ x|) * moduleTransl p f (ε * R'))
      (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul ((prop_convolApprox_tendsto hp hpt hf).comp h1)
      (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (∫ x, |ρ x|))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact w1pDens_convolApprox_le hint hs hρ1 hp hpt hf hε

/-- Convergence dominée dans `L^p`, `p < ∞`. -/
private lemma w1pDens_tendsto_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) {F : ℕ → α → ℝ} {G : α → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hG : MemLp G p μ)
    (hbd : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ G x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  set r := p.toReal with hr_def
  have hr0 : 0 < r := ENNReal.toReal_pos hp0 hpt
  have e : ∀ n, eLpNorm (F n) p μ = (∫⁻ x, ‖F n x‖ₑ ^ r ∂μ) ^ (1 / r) := fun n =>
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt (hF n)
  simp_rw [e]
  have hfin : ∫⁻ x, ‖G x‖ₑ ^ r ∂μ ≠ ∞ := by
    have := hG.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hG.aestronglyMeasurable] at this
    exact (ENNReal.rpow_lt_top_iff_of_pos (by positivity)).1 this |>.ne
  have hL : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ r ∂μ) atTop (𝓝 (∫⁻ _x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖G x‖ₑ ^ r)
      (fun n => ((hF n).enorm.pow_const r)) (fun n => ?_) hfin ?_
    · filter_upwards [hbd n] with x hx
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hx.trans (Real.le_norm_self _))
    · filter_upwards [hlim] with x hx
      have h1 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 ‖(0 : ℝ)‖ₑ) :=
        (continuous_enorm.tendsto 0).comp hx
      rw [enorm_zero] at h1
      have h2 := (ENNReal.continuous_rpow_const (y := r)).tendsto 0 |>.comp h1
      rwa [ENNReal.zero_rpow_of_pos hr0] at h2
  rw [lintegral_zero] at hL
  have h3 := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto 0 |>.comp hL
  rwa [ENNReal.zero_rpow_of_pos (by positivity)] at h3

/-- **Troncature.** Une fonction `φ` de classe `C^∞` sur `ℝ^d`, avec `φ, ∂ᵢφ ∈ L^p` (`p < ∞`),
est limite dans `W^{1,p}` de fonctions test `χ(x/(n+1)) φ(x)`. -/
private lemma w1pDens_troncature {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {φ : ℝᵈ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφp : MemLp φ p)
    (hdφ : ∀ i : Fin d, MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) p) :
    ∃ ψ : ℕ → 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ),
      Tendsto (fun n => eLpNorm (⇑(ψ n) - φ) p) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm (fun x => fderiv ℝ (ψ n) x
        (EuclideanSpace.single i (1 : ℝ)) - fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) p)
          atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  let χ : ContDiffBump (0 : ℝᵈ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := χ.contDiff
  have hχ1 : ContDiff ℝ 1 χ := χ.contDiff
  obtain ⟨C, hC⟩ := (hχ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (χ.hasCompactSupport.fderiv ℝ)
  set s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hs_def
  have hs0 : ∀ n, 0 < s n := fun n => by positivity
  have hs1 : ∀ n, s n ≤ 1 := fun n => by
    rw [hs_def, div_le_one (by positivity)]
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  set c : ℕ → ℝᵈ → ℝ := fun n x => χ (s n • x) with hc_def
  have hc : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (c n) := fun n => hχ.comp (contDiff_const_smul _)
  have hcs : ∀ n, HasCompactSupport (c n) := fun n =>
    χ.hasCompactSupport.comp_smul (hs0 n).ne'
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hχd : Differentiable ℝ χ := hχ1.differentiable one_ne_zero
  -- dérivée de `c n`
  have hcD : ∀ n x, HasFDerivAt (c n) ((fderiv ℝ χ (s n • x)).comp
      (s n • ContinuousLinearMap.id ℝ ℝᵈ)) x := fun n x =>
    (hχd _).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul (s n))
  set D : ℕ → ℝᵈ → ℝᵈ →L[ℝ] ℝ := fun n x => (fderiv ℝ χ (s n • x)).comp
      (s n • ContinuousLinearMap.id ℝ ℝᵈ) with hD_def
  have hDv : ∀ n x (v : ℝᵈ), D n x v = s n * fderiv ℝ χ (s n • x) v := fun n x v => by
    simp [hD_def]
  have hDb : ∀ n x (v : ℝᵈ), |D n x v| ≤ s n * C * ‖v‖ := fun n x v => by
    rw [hDv, abs_mul, abs_of_pos (hs0 n), mul_assoc]
    gcongr
    exact ((fderiv ℝ χ (s n • x)).le_opNorm v).trans (by gcongr; exact hC _)
  let ψ : ℕ → 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ) := fun n =>
    ⟨fun x => c n x * φ x, (hc n).mul hφ, (hcs n).mul_right, subset_univ _⟩
  have hψ : ∀ n x, ψ n x = c n x * φ x := fun _ _ => rfl
  have hψD : ∀ n x (v : ℝᵈ), fderiv ℝ (ψ n) x v = c n x * fderiv ℝ φ x v + φ x * D n x v := by
    intro n x v
    have h := ((hcD n x).mul (hφd x).hasFDerivAt).fderiv
    have he : (⇑(ψ n) : ℝᵈ → ℝ) = c n * φ := rfl
    rw [he, h]
    simp [smul_eq_mul, hDv]
  -- `c n x → 1`
  have hc01 : ∀ n x, 0 ≤ c n x ∧ c n x ≤ 1 := fun n x => ⟨χ.nonneg, χ.le_one⟩
  have hclim : ∀ x, ∀ᶠ n in atTop, c n x = 1 := by
    intro x
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    refine χ.one_of_mem_closedBall ?_
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg (hs0 n).le]
    change 1 / ((n : ℝ) + 1) * ‖x‖ ≤ 1
    rw [one_div, inv_mul_le_iff₀ (by positivity), mul_one]
    have := Nat.le_ceil ‖x‖
    have h2 : (⌈‖x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hslim : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨ψ, ?_, fun i => ?_⟩
  · refine w1pDens_tendsto_eLpNorm hp0 hpt (G := fun x => ‖φ x‖)
      (fun n => ((ψ n).continuous.sub hφd.continuous).aestronglyMeasurable) hφp.norm
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · rw [Pi.sub_apply, hψ, show c n x * φ x - φ x = (c n x - 1) * φ x by ring, norm_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hc01 n x]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hclim x] with n hn
      rw [Pi.sub_apply, hψ, hn, one_mul, sub_self]
  · set e := EuclideanSpace.single i (1 : ℝ) with he
    have hen : ‖e‖ = 1 := by simp [he]
    have hdc : Continuous fun x => fderiv ℝ φ x e :=
      (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    refine w1pDens_tendsto_eLpNorm hp0 hpt (G := fun x => ‖fderiv ℝ φ x e‖ + C * ‖φ x‖)
      (fun n => ?_) ((hdφ i).norm.add (hφp.norm.const_mul C))
      (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · have : Continuous fun x => fderiv ℝ (ψ n) x e :=
        (((hc n).mul hφ).continuous_fderiv (by simp)).clm_apply continuous_const
      exact (this.sub hdc).aestronglyMeasurable
    · rw [hψD, show c n x * fderiv ℝ φ x e + φ x * D n x e - fderiv ℝ φ x e =
        (c n x - 1) * fderiv ℝ φ x e + φ x * D n x e by ring]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hc01 n x]
      · rw [norm_mul, mul_comm C, Real.norm_eq_abs (D n x e)]
        gcongr
        refine (hDb n x e).trans ?_
        rw [hen, mul_one]
        have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
        exact mul_le_of_le_one_left hC0 (hs1 n)
    · have h1 : Tendsto (fun n => (c n x - 1) * fderiv ℝ φ x e) atTop (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hclim x] with n hn
        rw [hn, sub_self, zero_mul]
      have h2 : Tendsto (fun n => φ x * D n x e) atTop (𝓝 0) := by
        have h3 : Tendsto (fun n => s n * C * ‖e‖) atTop (𝓝 0) := by
          simpa using (hslim.mul_const C).mul_const ‖e‖
        have h4 : Tendsto (fun n => D n x e) atTop (𝓝 0) :=
          squeeze_zero_norm (fun n => (Real.norm_eq_abs _).le.trans (hDb n x e)) h3
        simpa using h4.const_mul (φ x)
      refine (h1.add h2).congr' (Eventually.of_forall fun n => ?_) |>.trans (by simp)
      rw [hψD]
      ring

/-- Dérivée d'une convolution `k ⋆ f`, `k ∈ C^1_c`, `f ∈ L^1_loc` :
`∂_v (k ⋆ f) = (∂_v k) ⋆ f`. -/
private lemma w1pDens_fderiv_convol {k f : ℝᵈ → ℝ} (hk : ContDiff ℝ 1 k) (hkc : HasCompactSupport k)
    (hf : LocallyIntegrable f) (x v : ℝᵈ) :
    fderiv ℝ (k ⋆ f) x v = ((fun t => fderiv ℝ k t v) ⋆ f) x := by
  rw [(hkc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) hk hf x).fderiv, convolution_def,
    convolution_def]
  have hint := (hkc.fderiv ℝ).convolutionExists_left ((lsmul ℝ ℝ).precompL ℝᵈ)
    (hk.continuous_fderiv one_ne_zero) hf x
  rw [ContinuousLinearMap.integral_apply hint]
  rfl

/-- Identité de la dérivée faible : si `∂_v f = g` au sens des distributions sur `ℝ^d` et
`k ∈ C^∞_c`, alors `(∂_v k) ⋆ f = k ⋆ g`. -/
private lemma w1pDens_convol_weak {f g : ℝᵈ → ℝ} (hf : LocallyIntegrable f)
    (hg : LocallyIntegrable g)
    {v : ℝᵈ} (H : ∂_{v} (Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝᵈ) f volume ⊤) =
      Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝᵈ) g volume ⊤)
    {k : ℝᵈ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hkc : HasCompactSupport k) (x : ℝᵈ) :
    ((fun t => fderiv ℝ k t v) ⋆ f) x = (k ⋆ g) x := by
  have hψc : ContDiff ℝ (⊤ : ℕ∞) (fun y => k (x - y)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hψs : HasCompactSupport (fun y => k (x - y)) :=
    hkc.comp_homeomorph (Homeomorph.subLeft x)
  let ψ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ) := ⟨fun y => k (x - y), hψc, hψs, subset_univ _⟩
  have hψ : ∀ y, ψ y = k (x - y) := fun _ => rfl
  have hkd : Differentiable ℝ k := hk.differentiable (by simp)
  have hdψ : ∀ y, (∂_{v} ψ) y = - fderiv ℝ k (x - y) v := by
    intro y
    rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
      TestFunction.fderivCLM_apply_of_le _ le_top]
    have h0 := (hkd (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    have h1 : HasFDerivAt (fun y => k (x - y))
        ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ ℝᵈ)) y := h0
    have he : (⇑ψ : ℝᵈ → ℝ) = fun y => k (x - y) := rfl
    rw [he, h1.fderiv]
    simp
  have H1 := congrArg (fun T => T ψ) H
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply (hf.locallyIntegrableOn _),
    Distribution.ofFun_apply (hg.locallyIntegrableOn _)] at H1
  rw [convolution_lsmul_swap, convolution_lsmul_swap]
  convert H1 using 2
  funext y
  rw [show ((-∂_{v} ψ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ)) y) = -(∂_{v} ψ) y from rfl,
    hdψ, neg_neg]

/-! ### Énoncés de densité -/

private lemma w1pDens_restrict_top :
    volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ) = volume := by
  simp

private lemma w1pDens_memLp_top {p : ℝ≥0∞}
    (f : Lp ℝ p (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ))) :
    MemLp (f : ℝᵈ → ℝ) p := by
  exact (Lp.memLp f).mono_measure w1pDens_restrict_top.ge

private lemma w1pDens_eLpNorm_top {p : ℝ≥0∞} (F : ℝᵈ → ℝ) :
    eLpNorm F p (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)) =
      eLpNorm F p volume := by
  rw [w1pDens_restrict_top]

private lemma w1pDens_ae_top {f g : ℝᵈ → ℝ}
    (h : f =ᵐ[volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)] g) : f =ᵐ[volume] g := by
  rwa [w1pDens_restrict_top] at h

/-- Convergence dans `L^p(Ω) × L^p(Ω)^d` composante par composante. -/
private lemma w1pDens_tendsto_LpGrad {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {ι : Type*} {l : Filter ι} {w : ι → LpGrad Ω p} {u : LpGrad Ω p}
    (h1 : Tendsto (fun n => (w n).fst) l (𝓝 u.fst))
    (h2 : ∀ i, Tendsto (fun n => (w n).snd i) l (𝓝 (u.snd i))) : Tendsto w l (𝓝 u) := by
  have h3 : Tendsto (fun n => (w n).snd) l (𝓝 u.snd) := by
    have := ((PiLp.continuous_toLp p _).tendsto _).comp (tendsto_pi_nhds.2 h2)
    simpa [Function.comp_def] using this
  have e : ∀ x : LpGrad Ω p, WithLp.toLp p (x.fst, x.snd) = x := fun x => rfl
  have := ((WithLp.prod_continuous_toLp p _ _).tendsto _).comp (h1.prodMk_nhds h3)
  simpa only [Function.comp_def, e] using this

/-- Une fonction `φ` de classe `C^∞` avec `φ, ∂ᵢφ ∈ L^p(ℝ^d)` est dans `W^{1,p}_0(ℝ^d)`. -/
private lemma w1pDens_mem_W1p0 {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {w : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p} {φ : ℝᵈ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφp : MemLp φ p)
    (hdφ : ∀ i : Fin d, MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) p)
    (h1 : (w.fst : ℝᵈ → ℝ) =ᵐ[volume] φ)
    (h2 : ∀ i, (w.snd i : ℝᵈ → ℝ) =ᵐ[volume]
      fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) :
    w ∈ W1p0 ⊤ p := by
  obtain ⟨ψ, hψ1, hψ2⟩ := w1pDens_troncature Fact.out hp hφ hφp hdφ
  change w ∈ (LinearMap.range (testGrad ⊤ p)).topologicalClosure
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => testGrad ⊤ p (ψ n)) ?_
    (Eventually.of_forall fun n => ⟨ψ n, rfl⟩)
  refine w1pDens_tendsto_LpGrad ?_ fun i => ?_
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    simp only [w1pDens_eLpNorm_top]
    refine hψ1.congr fun n => eLpNorm_congr_ae ?_
    exact (w1pDens_ae_top (testGrad_fst ⊤ p (ψ n))).symm.sub h1.symm
  · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    simp only [w1pDens_eLpNorm_top]
    refine (hψ2 i).congr fun n => eLpNorm_congr_ae ?_
    exact (w1pDens_ae_top (testGrad_snd ⊤ p (ψ n) i)).symm.sub (h2 i).symm

/-- Version renforcée de `prop_testDenseWsp` : les approximations sont de plus dans
`W^{1,p}_0(ℝ^d)`. -/
private lemma w1pDens_approx {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : W1p (⊤ : TopologicalSpace.Opens ℝᵈ) p) {ρ : ℝᵈ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hρ1 : ∫ x, ρ x = 1) :
    ∃ U : ℝ → W1p (⊤ : TopologicalSpace.Opens ℝᵈ) p,
      (∀ ε > 0, ((U ε : LpGrad ⊤ p).fst : ℝᵈ → ℝ) =ᵐ[volume]
          (noyauEps ρ ε ⋆ ((u : LpGrad ⊤ p).fst : ℝᵈ → ℝ)) ∧
        (∀ i, ((U ε : LpGrad ⊤ p).snd i : ℝᵈ → ℝ) =ᵐ[volume] fun x =>
          fderiv ℝ (noyauEps ρ ε ⋆ ((u : LpGrad ⊤ p).fst : ℝᵈ → ℝ)) x
            (EuclideanSpace.single i (1 : ℝ))) ∧
        (U ε).1 ∈ W1p0 ⊤ p) ∧
      Tendsto U (𝓝[>] 0) (𝓝 u) := by
  obtain ⟨f, hf_def⟩ : ∃ f : ℝᵈ → ℝ, f = ((u : LpGrad ⊤ p).fst : ℝᵈ → ℝ) := ⟨_, rfl⟩
  obtain ⟨g, hg_def⟩ : ∃ g : Fin d → ℝᵈ → ℝ,
      g = fun i => ((u : LpGrad ⊤ p).snd i : ℝᵈ → ℝ) := ⟨_, rfl⟩
  have hgi : ∀ i, ((u : LpGrad ⊤ p).snd i : ℝᵈ → ℝ) = g i := fun i => by rw [hg_def]
  rw [← hf_def]
  have hf : MemLp f p := by rw [hf_def]; exact w1pDens_memLp_top _
  have hg : ∀ i, MemLp (g i) p := fun i => by rw [← hgi]; exact w1pDens_memLp_top _
  have hfl : LocallyIntegrable f := hf.locallyIntegrable Fact.out
  have hgl : ∀ i, LocallyIntegrable (g i) := fun i => (hg i).locallyIntegrable Fact.out
  have hW : ∀ i : Fin d, ∂_{EuclideanSpace.single i (1 : ℝ)}
      (Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝᵈ) f volume ⊤) =
        Distribution.ofFun (⊤ : TopologicalSpace.Opens ℝᵈ) (g i) volume ⊤ := fun i => by
    rw [hf_def, ← hgi]; exact mem_W1p.mp u.2 i
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hk : ∀ ε, ContDiff ℝ (⊤ : ℕ∞) (noyauEps ρ ε) := fun ε =>
    contDiff_const.mul (hρ.comp (contDiff_const_smul _))
  have hkc : ∀ ε, 0 < ε → HasCompactSupport (noyauEps ρ ε) := fun ε hε =>
    (hρc.comp_smul (inv_ne_zero hε.ne')).mul_left
  have hd : ∀ ε, 0 < ε → ∀ i x, fderiv ℝ (noyauEps ρ ε ⋆ f) x (EuclideanSpace.single i 1) =
      (noyauEps ρ ε ⋆ g i) x := fun ε hε i x => by
    rw [w1pDens_fderiv_convol ((hk ε).of_le (by simp)) (hkc ε hε) hfl,
      w1pDens_convol_weak hfl (hgl i) (hW i) (hk ε) (hkc ε hε)]
  have hφp : ∀ ε, 0 < ε → MemLp (noyauEps ρ ε ⋆ f) p := fun ε hε =>
    (prop_convolLp Fact.out (integrable_noyauEps hρi hε) hf).2.1
  have hφp' : ∀ ε, 0 < ε → MemLp (noyauEps ρ ε ⋆ f) p
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)) := fun ε hε => by
    rw [w1pDens_restrict_top]; exact hφp ε hε
  have hdp : ∀ ε, 0 < ε → ∀ i, MemLp (fun x => fderiv ℝ (noyauEps ρ ε ⋆ f) x
      (EuclideanSpace.single i 1)) p := fun ε hε i => by
    rw [show (fun x => fderiv ℝ (noyauEps ρ ε ⋆ f) x (EuclideanSpace.single i 1)) =
      noyauEps ρ ε ⋆ g i from funext (hd ε hε i)]
    exact (prop_convolLp Fact.out (integrable_noyauEps hρi hε) (hg i)).2.1
  have hdp' : ∀ ε, 0 < ε → ∀ i, MemLp (fun x => fderiv ℝ (noyauEps ρ ε ⋆ f) x
      (EuclideanSpace.single i 1)) p
      (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)) := fun ε hε i => by
    rw [w1pDens_restrict_top]; exact hdp ε hε i
  let w : ∀ ε : ℝ, 0 < ε → LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p := fun ε hε =>
    WithLp.toLp p ((hφp' ε hε).toLp _, WithLp.toLp p fun i => (hdp' ε hε i).toLp _)
  have hw1 : ∀ (ε : ℝ) (hε : 0 < ε), ((w ε hε).fst : ℝᵈ → ℝ) =ᵐ[volume] noyauEps ρ ε ⋆ f :=
    fun ε hε => w1pDens_ae_top (MemLp.coeFn_toLp (hφp' ε hε))
  have hw2 : ∀ (ε : ℝ) (hε : 0 < ε) i, ((w ε hε).snd i : ℝᵈ → ℝ) =ᵐ[volume]
      fun x => fderiv ℝ (noyauEps ρ ε ⋆ f) x (EuclideanSpace.single i 1) :=
    fun ε hε i => w1pDens_ae_top (MemLp.coeFn_toLp (hdp' ε hε i))
  have hw0 : ∀ (ε : ℝ) (hε : 0 < ε), w ε hε ∈ W1p0 ⊤ p := fun ε hε =>
    w1pDens_mem_W1p0 hp (((hkc ε hε).contDiff_convolution_left (lsmul ℝ ℝ) (hk ε) hfl))
      (hφp ε hε) (hdp ε hε) (hw1 ε hε) (hw2 ε hε)
  let U : ℝ → W1p (⊤ : TopologicalSpace.Opens ℝᵈ) p := fun ε =>
    if hε : 0 < ε then ⟨w ε hε, rem_bcDirichlet ⊤ p (hw0 ε hε)⟩ else u
  have hU : ∀ (ε : ℝ) (hε : 0 < ε), (U ε).1 = w ε hε := fun ε hε => by
    simp [U, hε]
  refine ⟨U, fun ε hε => ⟨?_, fun i => ?_, ?_⟩, ?_⟩
  · rw [hU ε hε]; exact hw1 ε hε
  · rw [hU ε hε]; exact hw2 ε hε i
  · rw [hU ε hε]; exact hw0 ε hε
  rw [tendsto_subtype_rng]
  have hlim : Tendsto (fun ε => (U ε).1) (𝓝[>] 0) (𝓝 u.1) := by
    refine w1pDens_tendsto_LpGrad ?_ fun i => ?_
    · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      simp only [w1pDens_eLpNorm_top]
      rw [← hf_def]
      refine (w1pDens_tendsto_convol hρ.continuous hρc hρ1 Fact.out hp hf).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine eLpNorm_congr_ae ?_
      rw [hU ε hε]
      exact (hw1 ε hε).symm.sub EventuallyEq.rfl
    · rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      simp only [w1pDens_eLpNorm_top]
      rw [hgi]
      refine (w1pDens_tendsto_convol hρ.continuous hρc hρ1 Fact.out hp (hg i)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      refine eLpNorm_congr_ae ?_
      rw [hU ε hε]
      refine (EventuallyEq.trans ?_ (hw2 ε hε i).symm).sub EventuallyEq.rfl
      exact Eventually.of_forall fun x => (hd ε hε i x).symm
  exact hlim

/-- **Prop. `prop:testDenseWsp`, `s = 1`, convergence.** Soient `p ∈ [1, ∞[`,
`u = (f, ∇f) ∈ W^{1,p}(ℝ^d)` et `ρ ∈ 𝓓(ℝ^d)` d'intégrale `1`. Alors `ρ_ε ⋆ f` (lisse, munie de
son gradient classique) est dans `W^{1,p}(ℝ^d)` et converge vers `u` dans `W^{1,p}(ℝ^d)` lorsque
`ε → 0⁺`. Preuve : `∂ᵢ(ρ_ε ⋆ f) = (∂ᵢρ_ε) ⋆ f = ρ_ε ⋆ ∂ᵢf` (identité de la dérivée faible testée
contre `ρ_ε(x - ·)`), et `‖ρ_ε ⋆ h - h‖_p ≤ ‖ρ‖_1 ω_p(εR)` (variante de `lem:convolTranslat`
pour `ρ` de signe quelconque). -/
theorem prop_testDenseWsp {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Sobolev1 (⊤ : TopologicalSpace.Opens ℝᵈ) p) {ρ : ℝᵈ → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hρ1 : ∫ x, ρ x = 1) :
    ∃ U : ℝ → Sobolev1 (⊤ : TopologicalSpace.Opens ℝᵈ) p,
      (∀ ε > 0, ((U ε).val : ℝᵈ → ℝ) =ᵐ[volume] (noyauEps ρ ε ⋆ (u.val : ℝᵈ → ℝ)) ∧
        ∀ i, ((U ε).grad i : ℝᵈ → ℝ) =ᵐ[volume] fun x =>
          fderiv ℝ (noyauEps ρ ε ⋆ (u.val : ℝᵈ → ℝ)) x (EuclideanSpace.single i (1 : ℝ))) ∧
      Tendsto U (𝓝[>] 0) (𝓝 u) := by
  obtain ⟨U, hU, hlim⟩ := w1pDens_approx hp u hρ hρc hρ1
  exact ⟨U, fun ε hε => ⟨(hU ε hε).1, (hU ε hε).2.1⟩, hlim⟩

/-- **Prop. `prop:testDenseWsp`, `s = 1`, densité.** Pour `p ∈ [1, ∞[`, `𝓓(ℝ^d)` est dense dans
`W^{1,p}(ℝ^d)`, i.e. `W^{1,p}_0(ℝ^d) = W^{1,p}(ℝ^d)`.
Preuve (différente du cours, ordre inversé) : on régularise d'abord (`ρ_ε ⋆ f` est `C^∞`, avec ses
dérivées dans `L^p`), puis on tronque par `χ(x/(n+1))`, `χ` fonction plateau (convergence
dominée). -/
theorem prop_testDenseWsp_dense {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    W1p0 (⊤ : TopologicalSpace.Opens ℝᵈ) p = W1p ⊤ p := by
  refine le_antisymm (rem_bcDirichlet ⊤ p) fun u hu => ?_
  let χ : ContDiffBump (0 : ℝᵈ) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨U, hU, hlim⟩ := w1pDens_approx hp ⟨u, hu⟩ (χ.contDiff_normed (μ := volume))
    (χ.hasCompactSupport_normed (μ := volume)) (χ.integral_normed (μ := volume))
  exact (rem_bcDirichlet_isClosed ⊤ p).mem_of_tendsto (tendsto_subtype_rng.1 hlim)
    (eventually_mem_nhdsWithin.mono fun ε hε => (hU ε hε).2.2)

/-- `f ∈ L^p(ℝ^d) ⇒ f|_Ω ∈ L^p(Ω)`. -/
private lemma w1pDens_memLp_restr (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞}
    (f : Lp ℝ p (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ))) :
    MemLp (f : ℝᵈ → ℝ) p (volume.restrict (Ω : Set ℝᵈ)) :=
  (w1pDens_memLp_top f).restrict _

/-- Restriction `L^p(ℝ^d) → L^p(Ω)`, application linéaire continue (de norme `≤ 1`). -/
private noncomputable def w1pDens_restrLp (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] :
    Lp ℝ p (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ)) →L[ℝ]
      Lp ℝ p (volume.restrict (Ω : Set ℝᵈ)) :=
  LinearMap.mkContinuous
    { toFun := fun f => (w1pDens_memLp_restr Ω f).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine EventuallyEq.trans ?_ (Lp.coeFn_add _ _).symm
        refine EventuallyEq.trans (ae_restrict_of_ae (w1pDens_ae_top (Lp.coeFn_add f g))) ?_
        exact (MemLp.coeFn_toLp _).symm.add (MemLp.coeFn_toLp _).symm
      map_smul' := fun c f => by
        refine Lp.ext ?_
        refine (MemLp.coeFn_toLp _).trans ?_
        refine EventuallyEq.trans ?_ (Lp.coeFn_smul _ _).symm
        refine EventuallyEq.trans (ae_restrict_of_ae (w1pDens_ae_top (Lp.coeFn_smul c f))) ?_
        exact (MemLp.coeFn_toLp _).symm.const_smul c }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_toLp]
      rw [Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure _ ?_)
      exact Measure.restrict_mono (subset_univ _) le_rfl

private lemma w1pDens_restrLp_coe (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict ((⊤ : TopologicalSpace.Opens ℝᵈ) : Set ℝᵈ))) :
    (w1pDens_restrLp Ω p f : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] f :=
  MemLp.coeFn_toLp (w1pDens_memLp_restr Ω f)

/-- Restriction `L^p(ℝ^d) × L^p(ℝ^d)^d → L^p(Ω) × L^p(Ω)^d`. -/
private noncomputable def w1pDens_restr (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p →L[ℝ] LpGrad Ω p :=
  (WithLp.prodContinuousLinearEquiv p ℝ _ _).symm.toContinuousLinearMap ∘L
    ((w1pDens_restrLp Ω p).prodMap
      ((PiLp.continuousLinearEquiv p ℝ _).symm.toContinuousLinearMap ∘L
        ContinuousLinearMap.pi (fun i => w1pDens_restrLp Ω p ∘L ContinuousLinearMap.proj i) ∘L
        (PiLp.continuousLinearEquiv p ℝ _).toContinuousLinearMap)) ∘L
    (WithLp.prodContinuousLinearEquiv p ℝ _ _).toContinuousLinearMap

private lemma w1pDens_restr_fst (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p) :
    (w1pDens_restr Ω p w).fst = w1pDens_restrLp Ω p w.fst := rfl

private lemma w1pDens_restr_snd (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (w : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p) (i : Fin d) :
    (w1pDens_restr Ω p w).snd i = w1pDens_restrLp Ω p (w.snd i) := rfl

/-- Restriction à `Ω` d'une fonction test de `ℝ^d` : `φ ↦ (φ|_Ω, ∇φ|_Ω)`. -/
noncomputable def restrGrad (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ) →ₗ[ℝ] LpGrad Ω p :=
  (w1pDens_restr Ω p).toLinearMap ∘ₗ testGrad ⊤ p

private lemma w1pDens_restrGrad_apply (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ)) :
    restrGrad Ω p φ = w1pDens_restr Ω p (testGrad ⊤ p φ) := rfl

theorem restrGrad_fst (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ)) :
    ((restrGrad Ω p φ).fst : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)] φ :=
  (w1pDens_restrLp_coe Ω p _).trans
    (ae_restrict_of_ae (w1pDens_ae_top (testGrad_fst ⊤ p φ)))

theorem restrGrad_snd (Ω : TopologicalSpace.Opens ℝᵈ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ)) (i : Fin d) :
    ((restrGrad Ω p φ).snd i : ℝᵈ → ℝ) =ᵐ[volume.restrict (Ω : Set ℝᵈ)]
      fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
  (w1pDens_restrLp_coe Ω p _).trans
    (ae_restrict_of_ae (w1pDens_ae_top (testGrad_snd ⊤ p φ i)))

private lemma w1pDens_integral_congr {Ω : TopologicalSpace.Opens ℝᵈ} (ψ : 𝓓(Ω, ℝ))
    {F G : ℝᵈ → ℝ} (h : F =ᵐ[volume.restrict (Ω : Set ℝᵈ)] G) :
    ∫ x, ψ x • F x = ∫ x, ψ x • G x := by
  refine integral_congr_ae ?_
  have h' := (ae_restrict_iff' Ω.isOpen.measurableSet).1 h
  filter_upwards [h'] with x hx
  by_cases hxΩ : x ∈ (Ω : Set ℝᵈ)
  · rw [hx hxΩ]
  · simp [ψ.zero_on_compl hxΩ]

private lemma w1pDens_locInt {Ω : TopologicalSpace.Opens ℝᵈ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℝ p (volume.restrict (Ω : Set ℝᵈ))) : LocallyIntegrableOn (f : ℝᵈ → ℝ) Ω :=
  locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp f).locallyIntegrable Fact.out)

private lemma w1pDens_lineDeriv_apply {Ω : TopologicalSpace.Opens ℝᵈ} (ψ : 𝓓(Ω, ℝ)) (v x : ℝᵈ) :
    (∂_{v} ψ) x = fderiv ℝ ψ x v := by
  rw [TestFunction.lineDerivOp_eq_lineDerivCLM ℝ, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ le_top]

/-- La restriction envoie `W^{1,p}(ℝ^d)` dans `W^{1,p}(Ω)`. -/
private lemma w1pDens_restr_mem (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {w : LpGrad (⊤ : TopologicalSpace.Opens ℝᵈ) p} (hw : w ∈ W1p ⊤ p) :
    w1pDens_restr Ω p w ∈ W1p Ω p := by
  rw [mem_W1p]
  intro i
  have hW := mem_W1p.mp hw i
  ext ψ
  set e := EuclideanSpace.single i (1 : ℝ) with he
  let ψ' : 𝓓((⊤ : TopologicalSpace.Opens ℝᵈ), ℝ) :=
    ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, subset_univ _⟩
  have H := congrArg (fun T => T ψ') hW
  simp only at H
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply (w1pDens_locInt _),
    Distribution.ofFun_apply (w1pDens_locInt _)] at H
  rw [Distribution.lineDerivOp_apply_apply, Distribution.ofFun_apply (w1pDens_locInt _),
    Distribution.ofFun_apply (w1pDens_locInt _), w1pDens_restr_fst, w1pDens_restr_snd]
  have hd : ∀ x, (-∂_{e} ψ') x = (-∂_{e} ψ) x := by
    intro x
    change -(∂_{e} ψ') x = -(∂_{e} ψ) x
    rw [w1pDens_lineDeriv_apply, w1pDens_lineDeriv_apply]
    rfl
  calc ∫ x, (-∂_{e} ψ) x • (w1pDens_restrLp Ω p w.fst : ℝᵈ → ℝ) x
      = ∫ x, (-∂_{e} ψ) x • (w.fst : ℝᵈ → ℝ) x :=
        w1pDens_integral_congr _ (w1pDens_restrLp_coe Ω p _)
    _ = ∫ x, (-∂_{e} ψ') x • (w.fst : ℝᵈ → ℝ) x := by simp_rw [hd]
    _ = ∫ x, ψ' x • (w.snd i : ℝᵈ → ℝ) x := H
    _ = ∫ x, ψ x • (w.snd i : ℝᵈ → ℝ) x := rfl
    _ = ∫ x, ψ x • (w1pDens_restrLp Ω p (w.snd i) : ℝᵈ → ℝ) x :=
        (w1pDens_integral_congr _ (w1pDens_restrLp_coe Ω p _)).symm

/-- **Cor. `corol:testDenseWspO`, `s = 1`.** Soient `p ∈ [1, ∞[` et `Ω` ayant la propriété de
prolongement de Sobolev pour `p` (`ProlongementSobolev`, au lieu de « `Ω` régulier »,
\claudereport). Les restrictions `(φ|_Ω, ∇φ|_Ω)`, `φ ∈ 𝓓(ℝ^d)`, sont dans `W^{1,p}(Ω)` et y sont
denses. Preuve : `P u` est approché dans `W^{1,p}(ℝ^d)` par des fonctions test
(`prop_testDenseWsp_dense`), et la restriction à `Ω` est continue. -/
theorem corol_testDenseWspO (Ω : TopologicalSpace.Opens ℝᵈ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hP : ProlongementSobolev Ω p) :
    (LinearMap.range (restrGrad Ω p)).topologicalClosure = W1p Ω p := by
  obtain ⟨P, hP⟩ := hP
  refine le_antisymm ?_ fun u hu => ?_
  · refine Submodule.topologicalClosure_minimal _ ?_ (prop_SobolevBanach_isClosed Ω p)
    rintro _ ⟨φ, rfl⟩
    rw [w1pDens_restrGrad_apply]
    exact w1pDens_restr_mem Ω
      (rem_bcDirichlet ⊤ p (Submodule.le_topologicalClosure _ ⟨φ, rfl⟩))
  · have hPu : (P ⟨u, hu⟩).1 ∈ W1p0 ⊤ p := by
      rw [prop_testDenseWsp_dense hp]
      exact (P ⟨u, hu⟩).2
    have heq : w1pDens_restr Ω p (P ⟨u, hu⟩) = u := by
      have h1 := w1pDens_restr_mem Ω (P ⟨u, hu⟩).2
      have h2 : (⟨_, h1⟩ : W1p Ω p) = ⟨u, hu⟩ := by
        refine W1p_fst_injective Ω p (Lp.ext ?_)
        exact (w1pDens_restrLp_coe Ω p _).trans (hP ⟨u, hu⟩)
      exact congrArg Subtype.val h2
    have hPu' := hPu
    rw [W1p0, ← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hPu'
    have key : w1pDens_restr Ω p (P ⟨u, hu⟩).1 ∈
        closure (SetLike.coe (LinearMap.range (restrGrad Ω p))) := by
      refine map_mem_closure (w1pDens_restr Ω p).continuous hPu' ?_
      rintro _ ⟨φ, rfl⟩
      exact ⟨φ, w1pDens_restrGrad_apply Ω p φ⟩
    rw [heq] at key
    exact key

end M1Analyse
