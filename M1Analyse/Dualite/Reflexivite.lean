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
`Φ = inclusionInDoubleDual ℝ E : E → E^{**}` est bijective. -/
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
isométrique, donc injective. -/
theorem prop_conjugueDual_isometrie :
    Isometry (inclusionInDoubleDual ℝ E) ∧ Function.Injective (inclusionInDoubleDual ℝ E) :=
  ⟨(inclusionInDoubleDualLi (E := E) ℝ).isometry, (inclusionInDoubleDualLi (E := E) ℝ).injective⟩

/-- **Déf. `def:reflexif`, reformulation.** Comme `Φ` est injective (`prop:conjugueDual`),
`E` est réflexif si et seulement si `Φ` est surjective. -/
theorem def_reflexif_iff_surjective :
    Reflexif E ↔ Function.Surjective (inclusionInDoubleDual ℝ E) :=
  ⟨fun h => h.2, fun h => ⟨(prop_conjugueDual_isometrie E).2, h⟩⟩

/-- **Cor. `corol:faibleSepare`.** La topologie faible sur un evn `E` (topologie de
`WeakSpace ℝ E`) est séparée. -/
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

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **Rem. `rem:unifCvxHilbert` (Cas hilbertien).** Un espace préhilbertien réel satisfait
l'identité du parallélogramme, et est uniformément convexe au sens de `eq:unif_cvx_ball` :
`∀ ε > 0, ∃ δ > 0, ‖x‖ = ‖y‖ = 1, ‖x - y‖ ≥ ε ⇒ ‖(x+y)/2‖ ≤ 1 - δ`. De plus, pour tout
`x ∈ H`, la forme `⟨x, ·⟩` est un conjugué dual de `x` (cf. `prop:conjugueDual`). -/
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
Remarque : le cas d'égalité énoncé dans le cours n'est pas formalisé. -/
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

end Holder

end M1Analyse
