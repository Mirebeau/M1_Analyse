/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.MetricSpace.Completion
import M1Analyse.Completude.Prolongements
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Basic.Real.Sign
import Mathlib.Analysis.Convex.Uniform

/-!
# §3.2 Réflexivité (`subsec:reflexivite`)

Source : `Include/Dualite.tex`, sous-section `subsec:reflexivite`.

La fonction d'évaluation `Φ : E → E^{**}` du cours est `NormedSpace.inclusionInDoubleDual ℝ E`.
Mathlib ne possède pas (sous ce nom) de prédicat « espace réflexif » : on l'introduit
(`M1Analyse.Reflexif`), fidèlement à la définition du cours (`Φ` bijective). Les espaces `L^p`
sont ceux de Mathlib (`MemLp`, `eLpNorm`), avec exposants dans `ℝ≥0∞`.
-/

open Set Topology Filter Metric NormedSpace
open scoped ENNReal

namespace M1Analyse

section Bidual

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Déf. `def:reflexif` (Réflexivité).** L'evn `E` est réflexif si la fonction d'évaluation
`Φ = inclusionInDoubleDual ℝ E : E → E^{**}` est bijective.
Lien avec Mathlib : l'injection canonique est `NormedSpace.inclusionInDoubleDual`, qui vérifie
`Φ(x)(φ) = φ(x)` (`def_reflexif_eval`) ; Mathlib n'a pas (encore) de notion d'evn réflexif. -/
def Reflexif : Prop :=
  Function.Bijective (inclusionInDoubleDual ℝ E)

/-- **Déf. `def:reflexif`, fonction d'évaluation.** La fonction d'évaluation de Mathlib
`Φ = inclusionInDoubleDual ℝ E` satisfait `Φ(x)(φ) = φ(x)` pour tous `x ∈ E`, `φ ∈ E^*`. -/
theorem def_reflexif_eval (x : E) (φ : StrongDual ℝ E) :
    inclusionInDoubleDual ℝ E x φ = φ x :=
  rfl

/-- **Prop. `prop:conjugueDual` (Élément conjugué dual).** Pour tout `x ∈ E` il existe
`φ ∈ E^*` telle que `φ(x) = ‖x‖ ‖φ‖` et `‖φ‖ = ‖x‖`. -/
theorem prop_conjugueDual (x : E) :
    ∃ φ : StrongDual ℝ E, φ x = ‖x‖ * ‖φ‖ ∧ ‖φ‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp, by simp⟩
  · obtain ⟨g, hg1, hgx⟩ := exists_dual_vector ℝ x (norm_ne_zero_iff.2 hx)
    refine ⟨‖x‖ • g, ?_, ?_⟩
    · simp [hgx, norm_smul, hg1]
    · rw [norm_smul, hg1, norm_norm, mul_one]

/-- **Prop. `prop:conjugueDual`, conséquence.** La fonction d'évaluation `Φ : E → E^{**}` est
isométrique, donc injective.
Preuve (différente du cours) : isométrie de Mathlib `inclusionInDoubleDualLi`. -/
theorem prop_conjugueDual_isometrie :
    Isometry (inclusionInDoubleDual ℝ E) ∧ Function.Injective (inclusionInDoubleDual ℝ E) :=
  ⟨(inclusionInDoubleDualLi (E := E) ℝ).isometry, (inclusionInDoubleDualLi (E := E) ℝ).injective⟩

/-- **Déf. `def:reflexif`, reformulation.** Comme `Φ` est injective (`prop:conjugueDual`),
`E` est réflexif si et seulement si `Φ` est surjective. -/
theorem def_reflexif_iff_surjective :
    Reflexif E ↔ Function.Surjective (inclusionInDoubleDual ℝ E) :=
  ⟨fun h => h.2, fun h => ⟨(prop_conjugueDual_isometrie E).2, h⟩⟩

/-- **Cor. `corol:faibleSepare`.** La topologie faible sur un evn `E` (topologie de
`WeakSpace ℝ E`) est séparée.
Preuve (différente du cours) : instance `T2Space (WeakSpace ℝ E)` de Mathlib. -/
theorem corol_faibleSepare : T2Space (WeakSpace ℝ E) :=
  inferInstance

variable {E}

/-- **Cor. `corol:faibleFortBorne`.** Toute partie `A` d'un evn `E` faiblement bornée (i.e.
`{φ(x) | x ∈ A}` est bornée pour toute `φ ∈ E^*`) est bornée. -/
theorem corol_faibleFortBorne (A : Set E)
    (hA : ∀ φ : StrongDual ℝ E, Bornology.IsBounded (φ '' A)) : Bornology.IsBounded A := by
  have h : ∀ φ : StrongDual ℝ E, ∃ C, ∀ a : A, ‖inclusionInDoubleDual ℝ E a φ‖ ≤ C := by
    intro φ
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 (hA φ)
    exact ⟨C, fun a => hC _ (mem_image_of_mem φ a.2)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus h
  refine isBounded_iff_forall_norm_le.2 ⟨C, fun x hx => ?_⟩
  have := hC ⟨x, hx⟩
  rwa [show ‖inclusionInDoubleDual ℝ E x‖ = ‖x‖ from
    (inclusionInDoubleDualLi (E := E) ℝ).norm_map x] at this

/-- **Cor. `corol:bidualComplete`.** L'adhérence `cl(Φ(E)) ⊆ E^{**}` de l'image d'un evn `E`
s'identifie à son complété : il existe une bijection isométrique `e` du complété
`UniformSpace.Completion E` sur `cl(Φ(E))` telle que `e(x) = Φ(x)` pour `x ∈ E`. -/
theorem corol_bidualComplete :
    ∃ e : UniformSpace.Completion E ≃ᵢ closure (range (inclusionInDoubleDual ℝ E)),
      ∀ x : E, (e x : StrongDual ℝ (StrongDual ℝ E)) = inclusionInDoubleDual ℝ E x := by
  set Φ := inclusionInDoubleDual ℝ E
  have : CompleteSpace (closure (range Φ)) := isClosed_closure.completeSpace_coe
  let ι' : E → closure (range Φ) := fun x => ⟨Φ x, subset_closure (mem_range_self x)⟩
  have hι' : Isometry ι' := by
    refine Isometry.of_dist_eq fun x y => ?_
    rw [Subtype.dist_eq]
    exact (prop_conjugueDual_isometrie E).1.dist_eq x y
  have hd' : DenseRange ι' := by
    rw [DenseRange, Subtype.dense_iff]
    have : (Subtype.val '' range ι') = range Φ := by
      ext y; simp [ι']
    rw [this]
  obtain ⟨e, he⟩ := prop_espaceComplete_unique ((↑) : E → UniformSpace.Completion E) ι'
    UniformSpace.Completion.coe_isometry hι' UniformSpace.Completion.denseRange_coe hd'
  exact ⟨e, fun x => by rw [he x]⟩

end Bidual

section MilmanPettis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pont entre la définition du cours de l'uniforme convexité (`eq:unif_cvx_ball`) :
« $\forall \varepsilon>0$, $\exists \delta>0$, $\forall x,y \in E$,
$(\|x\|=\|y\|=1$ et $\|x-y\| \geq \varepsilon) \Rightarrow \|\frac{x+y}2\| \leq 1-\delta$ »,
et la classe `UniformConvexSpace` de Mathlib (qui borne $\|x+y\|$ par $2-\delta$). -/
theorem unifCvx_iff_uniformConvexSpace :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ε ≤ ‖x - y‖ →
      ‖(1 / 2 : ℝ) • (x + y)‖ ≤ 1 - δ) ↔ UniformConvexSpace E := by
  have key : ∀ x y : E, ‖(1 / 2 : ℝ) • (x + y)‖ = ‖x + y‖ / 2 := fun x y => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; ring
  constructor
  · intro h
    refine ⟨fun ε hε => ?_⟩
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨2 * δ, by positivity, fun x hx y hy hxy => ?_⟩
    have := H x y hx hy hxy
    rw [key] at this
    linarith
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h.uniform_convex hε
    refine ⟨δ / 2, by positivity, fun x y hx hy hxy => ?_⟩
    have := H hx hy hxy
    rw [key]
    linarith

/-- **Th. `th:unifCvxReflex` (Milman–Pettis), AXIOME.** Un evn `E` est uniformément convexe si
`∀ ε > 0, ∃ δ > 0, ∀ x y, ‖x‖ = ‖y‖ = 1, ‖x - y‖ ≥ ε ⇒ ‖(x+y)/2‖ ≤ 1 - δ` (`eq:unif_cvx_ball`).
Tout espace de Banach uniformément convexe est réflexif.
Remarque : la preuve est admise dans le cours, et le théorème est absent de Mathlib (où il
figure en TODO) ; à la demande de l'auteur, l'énoncé est posé comme **axiome** Lean. Les
résultats qui en dépendent le mentionnent dans `#print axioms` (`M1Analyse.th_unifCvxReflex`).
L'hypothèse équivaut à `UniformConvexSpace E` de Mathlib (`unifCvx_iff_uniformConvexSpace`). -/
axiom th_unifCvxReflex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hE : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E, ‖x‖ = 1 → ‖y‖ = 1 → ε ≤ ‖x - y‖ →
      ‖(1 / 2 : ℝ) • (x + y)‖ ≤ 1 - δ) :
    Reflexif E

/-- Milman–Pettis (`th:unifCvxReflex`), formulé avec la classe `UniformConvexSpace` de Mathlib :
tout espace de Banach uniformément convexe est réflexif. -/
theorem th_unifCvxReflex_uniformConvexSpace [CompleteSpace E] [UniformConvexSpace E] :
    Reflexif E :=
  th_unifCvxReflex (unifCvx_iff_uniformConvexSpace.2 inferInstance)
end MilmanPettis

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Rem. `rem:unifCvxHilbert` (Cas hilbertien).** Un espace préhilbertien réel satisfait
l'identité du parallélogramme, et est uniformément convexe au sens de `eq:unif_cvx_ball` :
`∀ ε > 0, ∃ δ > 0, ‖x‖ = ‖y‖ = 1, ‖x - y‖ ≥ ε ⇒ ‖(x+y)/2‖ ≤ 1 - δ`. De plus, pour tout
`x ∈ H`, la forme `⟨x, ·⟩` est un conjugué dual de `x` (cf. `prop:conjugueDual`).
Preuve (différente du cours) : l'uniforme convexité est tirée de l'instance Mathlib
`UniformConvexSpace` des espaces préhilbertiens, et non de l'identité du parallélogramme. -/
theorem rem_unifCvxHilbert :
    (∀ x y : H, ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 → ε ≤ ‖x - y‖ →
      ‖(1 / 2 : ℝ) • (x + y)‖ ≤ 1 - δ) ∧
    (∀ x : H, innerSL ℝ x x = ‖x‖ * ‖innerSL ℝ x‖ ∧ ‖innerSL ℝ x‖ = ‖x‖) := by
  refine ⟨fun x y => parallelogram_law_with_norm ℝ x y, fun ε hε => ?_, fun x => ?_⟩
  · obtain ⟨δ, hδ, h⟩ := UniformConvexSpace.uniform_convex (E := H) hε
    refine ⟨δ / 2, by positivity, fun x y hx hy hxy => ?_⟩
    have := h hx hy hxy
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  · rw [innerSL_apply_norm, innerSL_apply_apply, real_inner_self_eq_norm_mul_norm]
    exact ⟨rfl, rfl⟩

end Hilbert

section Holder

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Th. `th:HolderIneq` (Inégalité de Hölder), inégalité.** Soient `p, q ∈ [1, ∞]` avec
`1/p + 1/q = 1`. Pour tous `f ∈ L^p(X, μ)` et `g ∈ L^q(X, μ)` on a `fg ∈ L^1` et
`∫ f g ≤ ‖f‖_p ‖g‖_q`.
Les cas d'égalité sont `th_HolderIneq_eq` (`1 < p < ∞`) et `th_HolderIneq_eq_one` (`p = 1`).
Preuve (différente du cours) : inégalité de Hölder de Mathlib (`eLpNorm_smul_le_mul_eLpNorm`),
sans passer par l'inégalité de Young (utilisée en revanche pour le cas d'égalité). -/
theorem th_HolderIneq {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) {f g : X → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (f * g) μ ∧
      ∫ x, f x * g x ∂μ ≤ (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal := by
  have : ENNReal.HolderTriple p q 1 := ⟨by rw [hpq, inv_one]⟩
  have hint : Integrable (f * g) μ := hf.integrable_mul hg
  refine ⟨hint, ?_⟩
  have hle : eLpNorm (f • g) 1 μ ≤ eLpNorm f p μ * eLpNorm g q μ :=
    eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable
  have hfg : (f • g) = f * g := rfl
  rw [hfg] at hle
  calc ∫ x, f x * g x ∂μ ≤ ‖∫ x, f x * g x ∂μ‖ := Real.le_norm_self _
    _ ≤ ∫ x, ‖f x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm (f * g) 1 μ).toReal := by
      change ∫ x, ‖(f * g) x‖ ∂μ = _
      rw [integral_norm_eq_lintegral_enorm hint.1, eLpNorm_one_eq_lintegral_enorm]
      exact hint.aestronglyMeasurable
    _ ≤ (eLpNorm f p μ * eLpNorm g q μ).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne) hle
    _ = _ := ENNReal.toReal_mul

/-- **Th. `th:HolderIneq` (Inégalité de Hölder), cas d'égalité, `1 < p < ∞`.** Soient
`p, q ∈ [1, ∞]` avec `1/p + 1/q = 1` et `1 < p < ∞`, `f ∈ L^p(X, μ)`, `g ∈ L^q(X, μ)`, et
supposons `‖f‖_p ‖g‖_q ≠ 0`. On a égalité dans `∫ f g ≤ ‖f‖_p ‖g‖_q` ssi
`f = λ sign(g) |g|^{q/p}` `μ`-presque partout, avec `λ > 0` (`λ` est noté `c` en Lean). -/
theorem th_HolderIneq_eq {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hp' : p < ∞)
    {f g : X → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfg : (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal ≠ 0) :
    ∫ x, f x * g x ∂μ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal ↔
      ∃ c : ℝ, 0 < c ∧
        f =ᵐ[μ] fun x => c * Real.sign (g x) * |g x| ^ (q.toReal / p.toReal) := by
  have : ENNReal.HolderConjugate p q := ⟨by rw [hpq, inv_one]⟩
  have hP1 : 1 < p.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp'.ne).2 hp
    simpa using this
  have hPQ : p.toReal.HolderConjugate q.toReal := ENNReal.HolderConjugate.toReal hP1
  have hq0 : q ≠ 0 := by
    intro h; rw [h, ENNReal.inv_zero, add_top] at hpq; exact ENNReal.top_ne_one hpq
  have hqtop : q ≠ ∞ := by
    have : 0 < q.toReal := hPQ.symm.pos
    exact (ENNReal.toReal_pos_iff.1 this).2.ne
  set P := p.toReal with hPdef
  set Q := q.toReal with hQdef
  set A := (eLpNorm f p μ).toReal with hAdef
  set B := (eLpNorm g q μ).toReal with hBdef
  have hP0 : 0 < P := hPQ.pos
  have hQ0 : 0 < Q := hPQ.symm.pos
  have hA : 0 < A := lt_of_le_of_ne ENNReal.toReal_nonneg (fun h => hfg (by rw [← h, zero_mul]))
  have hB : 0 < B := lt_of_le_of_ne ENNReal.toReal_nonneg (fun h => hfg (by rw [← h, mul_zero]))
  -- `∫ |f|^p = ‖f‖_p^p`
  have hIf : ∫ x, |f x| ^ P ∂μ = A ^ P := by
    have := lpNorm_eq_integral_norm_rpow_toReal (μ := μ) (by positivity : p ≠ 0) hp'.ne
      hf.aestronglyMeasurable
    rw [← toReal_eLpNorm] at this
    rw [← hAdef] at this
    rw [this, ← Real.rpow_mul (integral_nonneg fun x => by positivity),
      inv_mul_cancel₀ hP0.ne', Real.rpow_one]
    simp only [Real.norm_eq_abs, hPdef]
  have hIg : ∫ x, |g x| ^ Q ∂μ = B ^ Q := by
    have := lpNorm_eq_integral_norm_rpow_toReal (μ := μ) hq0 hqtop hg.aestronglyMeasurable
    rw [← toReal_eLpNorm] at this
    rw [← hBdef] at this
    rw [this, ← Real.rpow_mul (integral_nonneg fun x => by positivity),
      inv_mul_cancel₀ hQ0.ne', Real.rpow_one]
    simp only [Real.norm_eq_abs, hQdef]
  have hintF : Integrable (fun x => |f x| ^ P) μ := by
    simpa only [Real.norm_eq_abs] using hf.integrable_norm_rpow (by positivity) hp'.ne
  have hintG : Integrable (fun x => |g x| ^ Q) μ := by
    simpa only [Real.norm_eq_abs] using hg.integrable_norm_rpow hq0 hqtop
  have hintFG : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hQP : Q / P + 1 = Q := by
    have := hPQ.inv_add_inv_eq_one
    field_simp at this ⊢
    linarith
  constructor
  · intro heq
    set D : X → ℝ := fun x =>
      |f x| ^ P / (A ^ P * P) + |g x| ^ Q / (B ^ Q * Q) - f x * g x / (A * B) with hDdef
    have hD0 : ∀ x, 0 ≤ D x := by
      intro x
      have hy := Real.young_inequality_of_nonneg (div_nonneg (abs_nonneg (f x)) hA.le)
        (div_nonneg (abs_nonneg (g x)) hB.le) hPQ
      rw [Real.div_rpow (abs_nonneg _) hA.le, Real.div_rpow (abs_nonneg _) hB.le] at hy
      have h1 : f x * g x / (A * B) ≤ |f x| / A * (|g x| / B) := by
        rw [div_mul_div_comm, ← abs_mul]
        exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      simp only [hDdef, div_div] at hy ⊢
      linarith
    have hDint : Integrable D μ :=
      ((hintF.div_const _).add (hintG.div_const _)).sub (hintFG.div_const _)
    have hDzero : ∫ x, D x ∂μ = 0 := by
      have h12 : Integrable (fun x => |f x| ^ P / (A ^ P * P) + |g x| ^ Q / (B ^ Q * Q)) μ :=
        (hintF.div_const _).add (hintG.div_const _)
      simp only [hDdef]
      rw [integral_sub h12 (hintFG.div_const _),
        integral_add (hintF.div_const _) (hintG.div_const _), integral_div, integral_div,
        integral_div, hIf, hIg, heq]
      have := hPQ.inv_add_inv_eq_one
      have hAP : 0 < A ^ P := Real.rpow_pos_of_pos hA _
      have hBQ : 0 < B ^ Q := Real.rpow_pos_of_pos hB _
      field_simp
      field_simp at this
      linarith
    have hDae : D =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => hD0 x) hDint).1 hDzero
    refine ⟨A / B ^ (Q / P), div_pos hA (Real.rpow_pos_of_pos hB _), ?_⟩
    filter_upwards [hDae] with x hx
    simp only [Pi.zero_apply] at hx
    set a := |f x| / A
    set b := |g x| / B
    have ha : 0 ≤ a := div_nonneg (abs_nonneg _) hA.le
    have hb : 0 ≤ b := div_nonneg (abs_nonneg _) hB.le
    have hy := Real.young_inequality_of_nonneg ha hb hPQ
    have hy' : a ^ P / P + b ^ Q / Q = |f x| ^ P / (A ^ P * P) + |g x| ^ Q / (B ^ Q * Q) := by
      simp only [a, b, Real.div_rpow (abs_nonneg _) hA.le, Real.div_rpow (abs_nonneg _) hB.le,
        div_div]
    have h1 : f x * g x / (A * B) ≤ a * b := by
      simp only [a, b]
      rw [div_mul_div_comm, ← abs_mul]
      exact div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
    simp only [hDdef] at hx
    have hab : a * b = a ^ P / P + b ^ Q / Q := by linarith
    have hfgabs : f x * g x = |f x * g x| := by
      have : f x * g x / (A * B) = |f x * g x| / (A * B) := by
        have : |f x * g x| / (A * B) = a * b := by
          simp only [a, b]; rw [div_mul_div_comm, abs_mul]
        linarith
      have hAB : (A * B) ≠ 0 := by positivity
      field_simp at this
      exact this
    have hpow : a ^ P = b ^ Q := (Real.young_inequality_eq_iff_of_nonneg ha hb hPQ).1 hab
    have ha' : a = b ^ (Q / P) := by
      rw [← Real.rpow_rpow_inv ha hP0.ne', hpow, ← Real.rpow_mul hb, div_eq_mul_inv]
    have hfabs : |f x| = A / B ^ (Q / P) * |g x| ^ (Q / P) := by
      have : |f x| = A * a := by simp only [a]; field_simp
      rw [this, ha', Real.div_rpow (abs_nonneg _) hB.le]
      ring
    have hQP0 : 0 < Q / P := div_pos hQ0 hP0
    rcases lt_trichotomy (g x) 0 with hgx | hgx | hgx
    · rw [abs_mul, abs_of_neg hgx] at hfgabs
      have hf' : f x = -|f x| :=
        mul_right_cancel₀ hgx.ne (by linarith : f x * g x = (-|f x|) * g x)
      rw [Real.sign_of_neg hgx, hf', hfabs]
      ring
    · rw [hgx, abs_zero, Real.zero_rpow hQP0.ne', mul_zero, abs_eq_zero] at hfabs
      rw [hfabs, hgx, Real.sign_zero]; ring
    · rw [Real.sign_of_pos hgx, mul_one, ← hfabs]
      rw [abs_mul, abs_of_pos hgx] at hfgabs
      exact mul_right_cancel₀ hgx.ne' hfgabs
  · rintro ⟨c, hc, hfe⟩
    have hsg : ∀ y : ℝ, Real.sign y * y = |y| := by
      intro y
      rcases lt_trichotomy y 0 with h | h | h
      · rw [Real.sign_of_neg h, abs_of_neg h]; ring
      · rw [h]; simp
      · rw [Real.sign_of_pos h, abs_of_pos h]; ring
    -- `∫ f g = c ‖g‖_q^q`
    have hI1 : ∫ x, f x * g x ∂μ = c * B ^ Q := by
      rw [← hIg, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hfe] with x hx
      rw [hx]
      calc c * Real.sign (g x) * |g x| ^ (Q / P) * g x
          = c * (|g x| ^ (Q / P) * (Real.sign (g x) * g x)) := by ring
        _ = c * |g x| ^ Q := by
          rw [hsg, ← Real.rpow_add_one' (abs_nonneg _) (by rw [hQP]; exact hQ0.ne'), hQP]
    -- `‖f‖_p^p = c^p ‖g‖_q^q`
    have hI2 : A ^ P = c ^ P * B ^ Q := by
      rw [← hIf, ← hIg, ← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hfe] with x hx
      rw [hx, abs_mul, abs_mul, abs_of_pos hc, mul_assoc, Real.mul_rpow hc.le (by positivity),
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      congr 1
      rcases eq_or_ne (g x) 0 with h | h
      · rw [h, abs_zero, Real.zero_rpow (div_pos hQ0 hP0).ne', mul_zero,
          Real.zero_rpow hP0.ne', Real.zero_rpow hQ0.ne']
      · have : |Real.sign (g x)| = 1 := by
          rcases Real.sign_apply_eq_of_ne_zero _ h with h' | h' <;> rw [h'] <;> simp
        rw [this, one_mul, ← Real.rpow_mul (abs_nonneg _), div_mul_cancel₀ _ hP0.ne']
    have hAc : A = c * B ^ (Q / P) := by
      rw [← Real.rpow_rpow_inv hA.le hP0.ne', hI2, Real.mul_rpow (by positivity) (by positivity),
        Real.rpow_rpow_inv hc.le hP0.ne', ← Real.rpow_mul hB.le, div_eq_mul_inv]
    rw [hI1, hAc, mul_assoc, ← Real.rpow_add_one hB.ne', hQP]

/-- **Th. `th:HolderIneq` (Inégalité de Hölder), cas d'égalité, `p = 1`.** Soient
`p, q ∈ [1, ∞]` avec `1/p + 1/q = 1` et `p = 1` (donc `q = ∞`), `f ∈ L^1(X, μ)`,
`g ∈ L^∞(X, μ)`, et supposons `‖f‖_1 ‖g‖_∞ ≠ 0`. On a égalité dans `∫ f g ≤ ‖f‖_1 ‖g‖_∞`
ssi `g = λ sign(f)` `μ`-presque partout où `|f| > 0`, et `‖g‖_∞ = λ` (`λ` est noté `c`
en Lean). -/
theorem th_HolderIneq_eq_one {p q : ℝ≥0∞} (hpq : p⁻¹ + q⁻¹ = 1) (hp : p = 1)
    {f g : X → ℝ} (hf : MemLp f p μ) (hg : MemLp g q μ)
    (hfg : (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal ≠ 0) :
    ∫ x, f x * g x ∂μ = (eLpNorm f p μ).toReal * (eLpNorm g q μ).toReal ↔
      ∃ c : ℝ, (∀ᵐ x ∂μ, 0 < |f x| → g x = c * Real.sign (f x)) ∧
        (eLpNorm g q μ).toReal = c := by
  subst hp
  have hq : q = ∞ := by
    rw [inv_one] at hpq
    have : q⁻¹ = 0 :=
      (ENNReal.add_right_inj ENNReal.one_ne_top).1 (by rw [hpq, add_zero])
    simpa using this
  subst hq
  set A := (eLpNorm f 1 μ).toReal with hAdef
  set B := (eLpNorm g ∞ μ).toReal with hBdef
  have hIf : ∫ x, |f x| ∂μ = A := by
    rw [hAdef, toReal_eLpNorm, lpNorm_one_eq_integral_norm hf.aestronglyMeasurable]
    simp only [Real.norm_eq_abs]
  have hgB : ∀ᵐ x ∂μ, |g x| ≤ B := by
    have := ae_le_lpNorm_exponent_top hg
    rw [← toReal_eLpNorm] at this
    simpa only [Real.norm_eq_abs] using this
  have hintF : Integrable (fun x => |f x|) μ := (memLp_one_iff_integrable.1 hf).abs
  have hintFG : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  constructor
  · intro heq
    set D : X → ℝ := fun x => |f x| * B - f x * g x with hDdef
    have hD0 : 0 ≤ᵐ[μ] D := by
      filter_upwards [hgB] with x hx
      simp only [Pi.zero_apply, hDdef, sub_nonneg]
      calc f x * g x ≤ |f x * g x| := le_abs_self _
        _ = |f x| * |g x| := abs_mul _ _
        _ ≤ |f x| * B := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    have hDint : Integrable D μ := (hintF.mul_const _).sub hintFG
    have hDzero : ∫ x, D x ∂μ = 0 := by
      simp only [hDdef]
      rw [integral_sub (hintF.mul_const _) hintFG, integral_mul_const, hIf, heq, sub_self]
    have hDae : D =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hD0 hDint).1 hDzero
    refine ⟨B, ?_, rfl⟩
    filter_upwards [hDae] with x hx hfx
    simp only [hDdef, Pi.zero_apply, sub_eq_zero] at hx
    rcases lt_trichotomy (f x) 0 with h | h | h
    · rw [Real.sign_of_neg h]
      rw [abs_of_neg h] at hx
      have := mul_left_cancel₀ h.ne (by linarith : f x * g x = f x * (-B))
      linarith
    · rw [h, abs_zero] at hfx; exact absurd hfx (lt_irrefl 0)
    · rw [Real.sign_of_pos h, mul_one]
      rw [abs_of_pos h] at hx
      exact (mul_left_cancel₀ h.ne' hx).symm
  · rintro ⟨c, hgc, hBc⟩
    have : ∫ x, f x * g x ∂μ = ∫ x, |f x| * c ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [hgc] with x hx
      rcases lt_trichotomy (f x) 0 with h | h | h
      · rw [hx (abs_pos.2 h.ne), Real.sign_of_neg h, abs_of_neg h]; ring
      · rw [h]; simp
      · rw [hx (abs_pos.2 h.ne'), Real.sign_of_pos h, abs_of_pos h]; ring
    rw [this, integral_mul_const, hIf, hBc]

end Holder

end M1Analyse
