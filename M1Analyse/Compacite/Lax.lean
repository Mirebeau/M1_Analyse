/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Preuve du lemme de Lax (`lem:chgVarLax`, `subsec:Brouwer`)

Pour `φ ∈ C²(ℝᵈ, ℝᵈ)` égale à l'identité hors de la boule unité fermée et `f` lisse à support
compact, `∫ f = ∫ (f ∘ φ) det Dφ`.

Preuve (différente du cours, qui ne traite que `d = 2`) : par homotopie. On pose `ψ = φ - id`,
`F(t, x) = f(x + t ψ x) det(I + t Dψ x)` (`FF`). Sa dérivée en `t` (`GG`) s'écrit, par
multilinéarité du déterminant, dérivation composée et alternance,
`∑ₖ det(jacobienne de y ↦ y + t ψ y, ligne k remplacée par ∇hₖ)`, `hₖ = (f ∘ φₜ) ψₖ`. Par
l'identité de Piola et intégration par parties, son intégrale est nulle
(`integral_det_update_grad_eq_zero`), donc `t ↦ ∫ F(t, ·)` est constante (dérivation sous
l'intégrale, `integral_eq_of_hasDerivAt`).
-/

open Matrix

namespace M1Analyse.LaxAux

variable {d : ℕ}

private noncomputable def detCML (d : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin d => Fin d → ℝ) ℝ :=
  { (Matrix.detRowAlternating : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ).toMultilinearMap with
    cont := by
      change Continuous fun M : Fin d → Fin d → ℝ => (Matrix.of M).det
      exact (continuous_id.matrix_det) }

@[simp] private lemma detCML_apply (M : Fin d → Fin d → ℝ) : detCML d M = (Matrix.of M).det := rfl

private lemma detCML_swap (M : Fin d → Fin d → ℝ) {i k : Fin d} (h : i ≠ k) :
    detCML d (M ∘ Equiv.swap i k) = - detCML d M :=
  (Matrix.detRowAlternating : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ).map_swap M h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ligne `i` de la « jacobienne » de `c` relativement à la famille `b`. -/
private noncomputable def gradRow (c : E → ℝ) (b : Fin d → E) (y : E) : Fin d → ℝ :=
  fun l => fderiv ℝ c y (b l)

/-- Ligne de dérivées secondes. -/
private noncomputable def hessRow (c : E → ℝ) (b : Fin d → E) (x : E) : E →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun l =>
    (ContinuousLinearMap.apply ℝ ℝ (b l)).comp (fderiv ℝ (fderiv ℝ c) x)

private lemma hasFDerivAt_gradRow {c : E → ℝ} (hc : ContDiff ℝ 2 c) (b : Fin d → E) (x : E) :
    HasFDerivAt (gradRow c b) (hessRow c b x) x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  refine hasFDerivAt_pi.2 fun l => ?_
  convert hd.hasFDerivAt.clm_apply (hasFDerivAt_const (b l) x) using 1
  · ext v; rfl
  · ext v; simp

/-- **Identité de Piola** (forme par lignes) : les cofacteurs de la ligne `k` d'une jacobienne
`C²` sont à divergence nulle. -/
private theorem piola (c : Fin d → E → ℝ) (hc : ∀ i, ContDiff ℝ 2 (c i)) (b : Fin d → E)
    (k : Fin d) (x : E) :
    ∑ j, fderiv ℝ (fun y => detCML d
      (Function.update (fun i => gradRow (c i) b y) k (Pi.single j 1))) x (b j) = 0 := by
  classical
  set M0 : Fin d → Fin d → ℝ := fun i => gradRow (c i) b x
  -- derivative of each row
  have hrow : ∀ j i, HasFDerivAt
      (fun y => Function.update (fun i => gradRow (c i) b y) k (Pi.single j 1) i)
      (if i = k then 0 else hessRow (c i) b x) x := by
    intro j i
    by_cases hik : i = k
    · subst hik
      simp only [Function.update_self, ite_true]
      exact hasFDerivAt_const (Pi.single j (1:ℝ) : Fin d → ℝ) x
    · simpa [Function.update_of_ne hik, hik] using hasFDerivAt_gradRow (hc i) b x
  have hder : ∀ j, fderiv ℝ (fun y => detCML d
      (Function.update (fun i => gradRow (c i) b y) k (Pi.single j 1))) x (b j) =
      ∑ i, if i = k then 0 else detCML d (Function.update (Function.update M0 k (Pi.single j 1)) i
        (hessRow (c i) b x (b j))) := by
    intro j
    rw [(HasFDerivAt.multilinear_comp (f := detCML d) (hrow j)).fderiv]
    simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik
      simp only [ite_true, _root_.zero_apply, map_zero]
    · simp only [hik, ite_false, ContinuousMultilinearMap.toContinuousLinearMap_apply]
      rfl
  simp_rw [hder]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hik : i = k
  · simp [hik]
  simp only [hik, ite_false]
  -- expand the Hessian row in the canonical basis
  set H : Fin d → Fin d → ℝ := fun j l => fderiv ℝ (fderiv ℝ (c i)) x (b j) (b l)
  have hsymm : ∀ j l, H j l = H l j := fun j l =>
    ((hc i).contDiffAt.isSymmSndFDerivAt (by simp)) (b j) (b l)
  set A : Fin d → Fin d → ℝ := fun j l =>
    detCML d (Function.update (Function.update M0 k (Pi.single j 1)) i (Pi.single l 1))
  have hA : ∀ j l, A j l = - A l j := by
    intro j l
    simp only [A]
    rw [← detCML_swap _ hik]
    congr 1
    funext m
    simp only [Function.comp_apply]
    by_cases hmi : m = i
    · rw [hmi, Equiv.swap_apply_left, Function.update_self, Function.update_of_ne (Ne.symm hik),
        Function.update_self]
    by_cases hmk : m = k
    · rw [hmk, Equiv.swap_apply_right, Function.update_self, Function.update_of_ne (Ne.symm hik),
        Function.update_self]
    · rw [Equiv.swap_apply_of_ne_of_ne hmi hmk, Function.update_of_ne hmi,
        Function.update_of_ne hmk, Function.update_of_ne hmi, Function.update_of_ne hmk]
  have hexp : ∀ j, detCML d (Function.update (Function.update M0 k (Pi.single j 1)) i
      (hessRow (c i) b x (b j))) = ∑ l, H j l * A j l := by
    intro j
    have : hessRow (c i) b x (b j) = ∑ l, H j l • (Pi.single l 1 : Fin d → ℝ) := by
      funext m
      simp [hessRow, H, Finset.sum_apply, Pi.single_apply]
    rw [this]
    have h1 := (detCML d).toMultilinearMap.map_update_sum Finset.univ i
      (fun l => H j l • (Pi.single l 1 : Fin d → ℝ)) (Function.update M0 k (Pi.single j 1))
    have h2 : ∀ l, (detCML d).toMultilinearMap (Function.update (Function.update M0 k
        (Pi.single j 1)) i (H j l • (Pi.single l 1 : Fin d → ℝ))) = H j l * A j l := by
      intro l
      rw [MultilinearMap.map_update_smul, smul_eq_mul]
      rfl
    simp only [h2] at h1
    exact h1
  simp_rw [hexp]
  have hS : ∑ j, ∑ l, H j l * A j l = - ∑ j, ∑ l, H j l * A j l := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hsymm l j, hA l j]
    ring
  linarith


private lemma contDiff_gradRow {c : E → ℝ} (hc : ContDiff ℝ 2 c) (b : Fin d → E) :
    ContDiff ℝ 1 (gradRow c b) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ c) := hc.fderiv_right (m := 1) (by norm_num)
  exact contDiff_pi.2 fun l => h1.clm_apply contDiff_const

/-- Cofacteur de la ligne `k`, colonne `j`. -/
private noncomputable def cof (c : Fin d → E → ℝ) (b : Fin d → E) (k j : Fin d) (x : E) : ℝ :=
  detCML d (Function.update (fun i => gradRow (c i) b x) k (Pi.single j 1))

private lemma contDiff_cof {c : Fin d → E → ℝ} (hc : ∀ i, ContDiff ℝ 2 (c i)) (b : Fin d → E)
    (k j : Fin d) : ContDiff ℝ 1 (cof c b k j) := by
  classical
  unfold cof
  refine (detCML d).contDiff.comp (contDiff_pi.2 fun i => ?_)
  by_cases hik : i = k
  · subst hik; simpa using (contDiff_const : ContDiff ℝ 1 fun _ : E => (Pi.single j 1 : Fin d → ℝ))
  · simpa [Function.update_of_ne hik] using contDiff_gradRow (hc i) b

/-- Développement selon la ligne `k`. -/
private lemma detCML_update_eq_sum (M : Fin d → Fin d → ℝ) (k : Fin d) (w : Fin d → ℝ) :
    detCML d (Function.update M k w) =
      ∑ j, w j * detCML d (Function.update M k (Pi.single j 1)) := by
  classical
  have hw : w = ∑ j, w j • (Pi.single j 1 : Fin d → ℝ) := by
    funext m; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  have h1 := (detCML d).toMultilinearMap.map_update_sum Finset.univ k
      (fun j => w j • (Pi.single j 1 : Fin d → ℝ)) M
  simp only [MultilinearMap.map_update_smul, smul_eq_mul] at h1
  exact h1

open MeasureTheory

/-- **Lemme clé** : l'intégrale d'un déterminant jacobien dont une ligne est le gradient d'une
fonction à support compact est nulle. -/
private theorem integral_det_update_grad_eq_zero [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {c : Fin d → E → ℝ} (hc : ∀ i, ContDiff ℝ 2 (c i)) (b : Fin d → E) (k : Fin d)
    {h : E → ℝ} (hh : ContDiff ℝ 1 h) (hhs : HasCompactSupport h) :
    ∫ x, detCML d (Function.update (fun i => gradRow (c i) b x) k (gradRow h b x)) ∂μ = 0 := by
  classical
  have hC := fun j => contDiff_cof hc b k j
  have hdh : Continuous (fderiv ℝ h) := hh.continuous_fderiv one_ne_zero
  have hint1 : ∀ j, Integrable (fun x => fderiv ℝ h x (b j) * cof c b k j x) μ := by
    intro j
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hdh.clm_apply continuous_const).mul (hC j).continuous
    · have h0 : HasCompactSupport (fderiv ℝ h) := hhs.fderiv (𝕜 := ℝ)
      have h1 : HasCompactSupport (fun x => fderiv ℝ h x (b j)) :=
        h0.comp_left (g := fun L : E →L[ℝ] ℝ => L (b j)) rfl
      exact h1.mul_right
  have hexp : ∀ x, detCML d (Function.update (fun i => gradRow (c i) b x) k (gradRow h b x)) =
      ∑ j, fderiv ℝ h x (b j) * cof c b k j x := fun x =>
    detCML_update_eq_sum _ k _
  simp_rw [hexp]
  change ∫ x, ∑ j, fderiv ℝ h x (b j) * cof c b k j x ∂μ = 0
  rw [integral_finsetSum _ fun j _ => hint1 j]
  have hibp : ∀ j, ∫ x, fderiv ℝ h x (b j) * cof c b k j x ∂μ =
      - ∫ x, h x * fderiv ℝ (cof c b k j) x (b j) ∂μ := by
    intro j
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (v := b j)
      (f := cof c b k j) (g := h) ?_ ?_ ?_ (fun x _ => ((hC j).differentiable one_ne_zero) x)
      (fun x _ => (hh.differentiable one_ne_zero) x)
    · simp only [mul_comm] at this ⊢; rw [this]
    · refine Continuous.integrable_of_hasCompactSupport ?_ hhs.mul_left
      exact (((hC j).continuous_fderiv one_ne_zero).clm_apply continuous_const).mul hh.continuous
    · simpa [mul_comm] using hint1 j
    · exact Continuous.integrable_of_hasCompactSupport ((hC j).continuous.mul hh.continuous)
        hhs.mul_left
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum]
  · simp_rw [← Finset.mul_sum]
    have hp : ∀ x, ∑ j, fderiv ℝ (cof c b k j) x (b j) = 0 := fun x => piola c hc b k x
    simp [hp]
  · intro j _
    refine Continuous.integrable_of_hasCompactSupport ?_ hhs.mul_right
    exact hh.continuous.mul (((hC j).continuous_fderiv one_ne_zero).clm_apply continuous_const)



/-- Ligne `k` remplacée par une combinaison des lignes : seul le `k`-ième coefficient reste. -/
private lemma detCML_update_comb (M : Fin d → Fin d → ℝ) (k : Fin d) (a : Fin d → ℝ) :
    detCML d (Function.update M k (∑ i, a i • M i)) = a k * detCML d M := by
  classical
  have h1 := (detCML d).toMultilinearMap.map_update_sum Finset.univ k (fun i => a i • M i) M
  simp only [MultilinearMap.map_update_smul, smul_eq_mul] at h1
  change detCML d _ = ∑ i, a i * detCML d (Function.update M k (M i)) at h1
  rw [h1, Finset.sum_eq_single k]
  · rw [Function.update_eq_self]
  · intro i _ hik
    have hz : detCML d (Function.update M k (M i)) = 0 :=
      (Matrix.detRowAlternating : (Fin d → ℝ) [⋀^Fin d]→ₗ[ℝ] ℝ).map_eq_zero_of_eq
        (Function.update M k (M i)) (i := i) (j := k) (by simp [Function.update_of_ne hik]) hik
    rw [hz, mul_zero]
  · simp

/-- **Constance d'une intégrale à paramètre** dont la dérivée en `t`, à support compact et
conjointement continue, est d'intégrale nulle. -/
private theorem integral_eq_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
    {F G : ℝ → E → ℝ} (hF : ∀ t, Continuous (F t)) (hFc : ∀ t, HasCompactSupport (F t))
    (hG : Continuous (Function.uncurry G)) {K : Set E} (hK : IsCompact K)
    (hGK : ∀ t, ∀ x ∉ K, G t x = 0) (hder : ∀ t x, HasDerivAt (fun s => F s x) (G t x) t)
    (hzero : ∀ t, ∫ x, G t x ∂μ = 0) : ∫ x, F 1 x ∂μ = ∫ x, F 0 x ∂μ := by
  have hD : ∀ t₀, HasDerivAt (fun t => ∫ x, F t x ∂μ) (∫ x, G t₀ x ∂μ) t₀ := by
    intro t₀
    obtain ⟨C, hC⟩ := ((isCompact_closedBall t₀ 1).prod hK).exists_bound_of_continuousOn
      hG.continuousOn
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := K.indicator fun _ => C)
      (Metric.closedBall_mem_nhds t₀ one_pos)
      (Filter.Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
      ((hF t₀).integrable_of_hasCompactSupport (hFc t₀))
      (hG.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
      ?_ ?_ ?_).2
    · refine Filter.Eventually.of_forall fun x t ht => ?_
      by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx]
        exact hC (t, x) ⟨ht, hx⟩
      · rw [hGK t x hx, Set.indicator_of_notMem hx]; simp
    · exact (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
    · exact Filter.Eventually.of_forall fun x t _ => hder t x
  have h0 : ∀ t, deriv (fun t => ∫ x, F t x ∂μ) t = 0 := fun t => by rw [(hD t).deriv, hzero]
  exact is_const_of_deriv_eq_zero (fun t => (hD t).differentiableAt) h0 1 0

/-! ### The Euclidean setting -/

section Euclid

local notation "Eu" => EuclideanSpace ℝ (Fin d)

/-- Base canonique de `ℝᵈ`. -/
private noncomputable abbrev eb (d : ℕ) : Fin d → EuclideanSpace ℝ (Fin d) :=
  fun l => EuclideanSpace.single l 1

/-- `det Dφ(x)` est le déterminant de la matrice des dérivées partielles `∂_l φ_i`. -/
private theorem det_fderiv_eq_det_partials (φ : Eu → Eu) (x : Eu) (hφ : DifferentiableAt ℝ φ x) :
    (fderiv ℝ φ x).det = (Matrix.of fun i l =>
      fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single l 1)).det := by
  rw [ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis]
  congr 1
  ext i l
  rw [LinearMap.toMatrix_apply]
  have h : fderiv ℝ (fun y => φ y i) x =
      (EuclideanSpace.proj i : Eu →L[ℝ] ℝ).comp (fderiv ℝ φ x) := by
    have := ((EuclideanSpace.proj i : Eu →L[ℝ] ℝ).hasFDerivAt).comp x hφ.hasFDerivAt
    exact this.fderiv
  simp [h]

private lemma contDiff_coord {n : WithTop ℕ∞} {g : Eu → Eu} (hg : ContDiff ℝ n g) (i : Fin d) :
    ContDiff ℝ n (fun y => g y i) :=
  (EuclideanSpace.proj i : Eu →L[ℝ] ℝ).contDiff.comp hg

private lemma fderiv_coord {g : Eu → Eu} {x : Eu} (hg : DifferentiableAt ℝ g x) (i : Fin d)
    (v : Eu) :
    fderiv ℝ (fun y => g y i) x v = fderiv ℝ g x v i := by
  have := ((EuclideanSpace.proj i : Eu →L[ℝ] ℝ).hasFDerivAt).comp x hg.hasFDerivAt
  rw [show (fun y => g y i) = (EuclideanSpace.proj i : Eu →L[ℝ] ℝ) ∘ g from rfl, this.fderiv]
  rfl

private lemma clm_apply_eq_sum (L : Eu →L[ℝ] ℝ) (w : Eu) : L w = ∑ i, w i * L (eb d i) := by
  have hw : w = ∑ i, w i • eb d i := by
    ext j; simp [Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_sum, map_smul, smul_eq_mul]

/-- Matrice jacobienne de `y ↦ y + t ψ(y)` en `x`, par lignes. -/
private noncomputable def Jac (ψ : Eu → Eu) (t : ℝ) (x : Eu) : Fin d → Fin d → ℝ :=
  fun i => Pi.single i 1 + t • gradRow (fun y => ψ y i) (eb d) x

private lemma Jac_apply {ψ : Eu → Eu} {x : Eu} (hψ : DifferentiableAt ℝ ψ x) (t : ℝ) (i l : Fin d) :
    Jac ψ t x i l = (eb d l + t • fderiv ℝ ψ x (eb d l)) i := by
  simp only [Jac, gradRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, fderiv_coord hψ]
  simp [Pi.single_apply, eq_comm]

private lemma gradRow_affine {ψ : Eu → Eu} (hψ : Differentiable ℝ ψ) (t : ℝ) (i : Fin d) (x : Eu) :
    gradRow (fun y => y i + t * ψ y i) (eb d) x = Jac ψ t x i := by
  have hψi : DifferentiableAt ℝ (fun y => ψ y i) x :=
    ((EuclideanSpace.proj i : Eu →L[ℝ] ℝ).differentiable.comp hψ) x
  have h := (EuclideanSpace.proj i : Eu →L[ℝ] ℝ).hasFDerivAt.add (hψi.hasFDerivAt.const_mul t)
  funext l
  simp only [gradRow]
  rw [show (fun y => y i + t * ψ y i) = ⇑(EuclideanSpace.proj i : Eu →L[ℝ] ℝ) +
    fun y => t * ψ y i from rfl, h.fderiv]
  simp [Jac, gradRow, Pi.single_apply, eq_comm]

variable {f : EuclideanSpace ℝ (Fin d) → ℝ}
  {ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}

/-- L'intégrande `F(t, x) = f(x + t ψ(x)) det(I + t Dψ(x))`. -/
private noncomputable def FF (f : Eu → ℝ) (ψ : Eu → Eu) (t : ℝ) (x : Eu) : ℝ :=
  f (x + t • ψ x) * detCML d (Jac ψ t x)

/-- Sa dérivée en `t`. -/
private noncomputable def GG (f : Eu → ℝ) (ψ : Eu → Eu) (t : ℝ) (x : Eu) : ℝ :=
  fderiv ℝ f (x + t • ψ x) (ψ x) * detCML d (Jac ψ t x) + f (x + t • ψ x) *
    ∑ k, detCML d (Function.update (Jac ψ t x) k (gradRow (fun y => ψ y k) (eb d) x))

private lemma hasDerivAt_FF (hf : Differentiable ℝ f) (t : ℝ) (x : Eu) :
    HasDerivAt (fun s => FF f ψ s x) (GG f ψ t x) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • ψ x) (ψ x) t := by
    simpa using ((hasDerivAt_id t).smul_const (ψ x)).const_add x
  have h2 : HasDerivAt (fun s => f (x + s • ψ x)) (fderiv ℝ f (x + t • ψ x) (ψ x)) t :=
    (hf _).hasFDerivAt.comp_hasDerivAt t h1
  have h3 : ∀ i, HasDerivAt (fun s => Jac ψ s x i) (gradRow (fun y => ψ y i) (eb d) x) t :=
    fun i => by
      simpa [Jac] using ((hasDerivAt_id t).smul_const
        (gradRow (fun y => ψ y i) (eb d) x)).const_add (Pi.single i (1 : ℝ))
  have h4 : HasFDerivAt (fun s => detCML d (fun i => Jac ψ s x i))
      (∑ i, ((detCML d).toContinuousLinearMap (fun j => Jac ψ t x j) i).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (gradRow (fun y => ψ y i) (eb d) x))) t :=
    HasFDerivAt.multilinear_comp (f := detCML d) (fun i => (h3 i).hasFDerivAt)
  have h5 : HasDerivAt (fun s => detCML d (Jac ψ s x))
      (∑ k, detCML d (Function.update (Jac ψ t x) k (gradRow (fun y => ψ y k) (eb d) x))) t := by
    convert h4.hasDerivAt using 1
    simp [ContinuousMultilinearMap.toContinuousLinearMap_apply]
  exact h2.mul h5

private lemma gradRow_h (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ) (t : ℝ) (k : Fin d)
    (x : Eu) :
    gradRow (fun y => f (y + t • ψ y) * ψ y k) (eb d) x =
      f (x + t • ψ x) • gradRow (fun y => ψ y k) (eb d) x +
        ψ x k • ∑ i, fderiv ℝ f (x + t • ψ x) (eb d i) • Jac ψ t x i := by
  have hΦ : HasFDerivAt (fun y => y + t • ψ y)
      (ContinuousLinearMap.id ℝ Eu + t • fderiv ℝ ψ x) x :=
    (hasFDerivAt_id x).add ((hψ x).hasFDerivAt.const_smul t)
  have hψk : DifferentiableAt ℝ (fun y => ψ y k) x :=
    ((EuclideanSpace.proj k : Eu →L[ℝ] ℝ).differentiable.comp hψ) x
  have hp := ((hf _).hasFDerivAt.comp x hΦ).mul hψk.hasFDerivAt
  funext l
  simp only [gradRow]
  rw [HasFDerivAt.fderiv (f := fun y => f (y + t • ψ y) * ψ y k) hp]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Pi.add_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [clm_apply_eq_sum (fderiv ℝ f (x + t • ψ x)) (eb d l + t • fderiv ℝ ψ x (eb d l))]
  simp only [Jac_apply (hψ x)]
  congr 2
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private lemma GG_eq (hf : Differentiable ℝ f) (hψ : Differentiable ℝ ψ) (t : ℝ) (x : Eu) :
    GG f ψ t x = ∑ k, detCML d (Function.update (Jac ψ t x) k
      (gradRow (fun y => f (y + t • ψ y) * ψ y k) (eb d) x)) := by
  simp only [gradRow_h hf hψ, ContinuousMultilinearMap.map_update_add,
    ContinuousMultilinearMap.map_update_smul, detCML_update_comb, smul_eq_mul,
    Finset.sum_add_distrib]
  rw [GG, clm_apply_eq_sum (fderiv ℝ f (x + t • ψ x)) (ψ x), Finset.sum_mul, Finset.mul_sum]
  have e : ∑ i, ψ x i * fderiv ℝ f (x + t • ψ x) (eb d i) * detCML d (Jac ψ t x) =
      ∑ k, ψ x k * (fderiv ℝ f (x + t • ψ x) (eb d k) * detCML d (Jac ψ t x)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [e]; ring

private lemma integrable_det_update [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsFiniteMeasureOnCompacts μ] {c : Fin d → E → ℝ} (hc : ∀ i, ContDiff ℝ 2 (c i))
    (b : Fin d → E) (k : Fin d) {h : E → ℝ} (hh : ContDiff ℝ 1 h) (hhs : HasCompactSupport h) :
    Integrable (fun x => detCML d (Function.update (fun i => gradRow (c i) b x) k
      (gradRow h b x))) μ := by
  have hgh : Continuous (gradRow h b) :=
    continuous_pi fun l => (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgc : Continuous fun x => (fun i => gradRow (c i) b x) :=
    continuous_pi fun i => (contDiff_gradRow (hc i) b).continuous
  refine Continuous.integrable_of_hasCompactSupport
    ((detCML d).cont.comp (hgc.update k hgh)) ?_
  refine (hhs.fderiv (𝕜 := ℝ)).mono fun x hx h0 => hx ?_
  have : gradRow h b x = 0 := by funext l; simp [gradRow, h0]
  simp only [this]
  exact (detCML d).map_update_zero _ _

private lemma gradRow_eq_zero_of_notMem {g : Eu → Eu} (hg : ∀ x ∉ Metric.closedBall 0 1, g x = 0)
    (i : Fin d) {x : Eu} (hx : x ∉ Metric.closedBall 0 1) :
    gradRow (fun y => g y i) (eb d) x = 0 := by
  have : (fun y => g y i) =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
    simp [hg y hy]
  funext l
  simp [gradRow, this.fderiv_eq]

private lemma detCML_one : detCML d (fun i => Pi.single i 1) = 1 := by
  rw [detCML_apply]
  convert Matrix.det_one (n := Fin d) (R := ℝ)
  ext i j
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

private lemma Jac_of_notMem (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0) (t : ℝ) {x : Eu}
    (hx : x ∉ Metric.closedBall 0 1) : Jac ψ t x = fun i => Pi.single i 1 := by
  funext i
  simp [Jac, gradRow_eq_zero_of_notMem hψB i hx]

private lemma continuous_Jac (hψ : ContDiff ℝ 1 ψ) :
    Continuous fun p : ℝ × Eu => Jac ψ p.1 p.2 := by
  unfold Jac
  refine continuous_pi fun i => continuous_const.add (continuous_fst.smul ?_)
  exact continuous_pi fun l => ((((contDiff_coord hψ i).continuous_fderiv one_ne_zero).comp
    continuous_snd).clm_apply continuous_const)

private lemma continuous_GG (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ) :
    Continuous (Function.uncurry (GG f ψ)) := by
  have hΦ : Continuous fun p : ℝ × Eu => p.2 + p.1 • ψ p.2 :=
    continuous_snd.add (continuous_fst.smul (hψ.continuous.comp continuous_snd))
  have hJ := continuous_Jac hψ
  have hg : ∀ k, Continuous fun p : ℝ × Eu => gradRow (fun y => ψ y k) (eb d) p.2 := fun k =>
    continuous_pi fun l => ((((contDiff_coord hψ k).continuous_fderiv one_ne_zero).comp
      continuous_snd).clm_apply continuous_const)
  change Continuous fun p : ℝ × Eu => GG f ψ p.1 p.2
  unfold GG
  refine ((((hf.continuous_fderiv one_ne_zero).comp hΦ).clm_apply
    (hψ.continuous.comp continuous_snd)).mul ((detCML d).cont.comp hJ)).add
    ((hf.continuous.comp hΦ).mul (continuous_finsetSum _ fun k _ => ?_))
  exact (detCML d).cont.comp (hJ.update k (hg k))

private lemma GG_of_notMem (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0) (t : ℝ) {x : Eu}
    (hx : x ∉ Metric.closedBall 0 1) : GG f ψ t x = 0 := by
  simp only [GG, gradRow_eq_zero_of_notMem hψB _ hx, hψB x hx, map_zero, zero_mul, zero_add]
  have h0 : ∀ k, detCML d (Function.update (Jac ψ t x) k 0) = 0 := fun k =>
    (detCML d).map_update_zero _ _
  simp only [h0, Finset.sum_const_zero, mul_zero]

private lemma FF_of_notMem (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0) (t : ℝ) {x : Eu}
    (hx : x ∉ Metric.closedBall 0 1) : FF f ψ t x = f x := by
  simp only [FF, Jac_of_notMem hψB t hx, hψB x hx, smul_zero, add_zero, detCML_one, mul_one]

private lemma continuous_FF (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 1 ψ) (t : ℝ) :
    Continuous (FF f ψ t) :=
  (hf.continuous.comp (continuous_id.add (hψ.continuous.const_smul t))).mul
    ((detCML d).cont.comp ((continuous_Jac hψ).comp (Continuous.prodMk_right t)))

private lemma hasCompactSupport_FF (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0)
    (hfc : HasCompactSupport f) (t : ℝ) : HasCompactSupport (FF f ψ t) := by
  refine HasCompactSupport.intro ((isCompact_closedBall 0 1).union hfc) fun x hx => ?_
  simp only [Set.mem_union, not_or] at hx
  rw [FF_of_notMem hψB t hx.1]
  exact image_eq_zero_of_notMem_tsupport hx.2

private lemma integral_GG (hf : ContDiff ℝ 1 f) (hψ : ContDiff ℝ 2 ψ)
    (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0) (t : ℝ) : ∫ x, GG f ψ t x = 0 := by
  have hf1 := hf.differentiable one_ne_zero
  have hψ1 := hψ.differentiable two_ne_zero
  have hψs : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_closedBall 0 1) hψB
  set c : Fin d → Eu → ℝ := fun i y => y i + t * ψ y i with hc_def
  set h : Fin d → Eu → ℝ := fun k y => f (y + t • ψ y) * ψ y k with hh_def
  have hc : ∀ i, ContDiff ℝ 2 (c i) := fun i =>
    (contDiff_coord contDiff_id i).add (contDiff_const.mul (contDiff_coord hψ i))
  have hh : ∀ k, ContDiff ℝ 1 (h k) := fun k =>
    (hf.comp (contDiff_id.add ((hψ.of_le (by norm_num)).const_smul t))).mul
      (contDiff_coord (hψ.of_le (by norm_num)) k)
  have hhs : ∀ k, HasCompactSupport (h k) := fun k =>
    (hψs.comp_left (g := fun v : Eu => v k) rfl).mul_left
  have e : ∀ x, GG f ψ t x = ∑ k, detCML d (Function.update (fun i => gradRow (c i) (eb d) x) k
      (gradRow (h k) (eb d) x)) := by
    intro x
    rw [GG_eq hf1 hψ1]
    simp only [hc_def, gradRow_affine hψ1]
    rfl
  simp_rw [e]
  rw [integral_finsetSum _ fun k _ => integrable_det_update volume hc (eb d) k (hh k) (hhs k)]
  exact Finset.sum_eq_zero fun k _ =>
    integral_det_update_grad_eq_zero volume hc (eb d) k (hh k) (hhs k)

/-- Lemme de Lax sous la forme `φ = id + ψ`. -/
private theorem lax_psi (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hψ : ContDiff ℝ 2 ψ)
    (hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0) : ∫ x, FF f ψ 1 x = ∫ x, f x := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  rw [integral_eq_of_hasDerivAt volume (continuous_FF hf hψ1) (hasCompactSupport_FF hψB hfc)
    (continuous_GG hf hψ1) (isCompact_closedBall 0 1) (fun t x hx => GG_of_notMem hψB t hx)
    (hasDerivAt_FF (hf.differentiable one_ne_zero)) (integral_GG hf hψ hψB)]
  congr 1
  funext x
  have : Jac ψ 0 x = fun i => Pi.single i 1 := by funext i; simp [Jac]
  simp only [FF, this, zero_smul, add_zero, detCML_one, mul_one]

end Euclid

end M1Analyse.LaxAux

namespace M1Analyse

open LaxAux

/-- Lemme de Lax (`lem:chgVarLax`), preuve ; voir `lem_chgVarLax` (`Compacite/Brouwer.lean`). -/
theorem lem_chgVarLax_proof {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ : ContDiff ℝ 2 φ)
    (hφB : ∀ x, x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 → φ x = x)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∫ x, f x = ∫ x, f (φ x) * (fderiv ℝ φ x).det := by
  set ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => φ y - y with hψ_def
  have hψ : ContDiff ℝ 2 ψ := hφ.sub contDiff_id
  have hψB : ∀ x ∉ Metric.closedBall 0 1, ψ x = 0 := fun x hx => by simp [hψ_def, hφB x hx]
  rw [← lax_psi (hf.of_le (by exact_mod_cast le_top)) hfc hψ hψB]
  congr 1
  funext x
  have hφx : x + (1 : ℝ) • ψ x = φ x := by simp [hψ_def]
  have hφd : DifferentiableAt ℝ φ x := hφ.differentiable two_ne_zero x
  rw [FF, hφx, det_fderiv_eq_det_partials φ x hφd]
  congr 1
  rw [← detCML_apply]
  congr 1
  funext i
  rw [← gradRow_affine (hψ.differentiable two_ne_zero) 1 i x]
  funext l
  simp only [gradRow]
  congr 2
  funext y
  simp [hψ_def]

end M1Analyse
