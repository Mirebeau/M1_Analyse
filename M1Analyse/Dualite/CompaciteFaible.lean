/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import M1Analyse.Dualite.Reflexivite

/-!
# §3.3 (suite) Polarité, compacité faible et optimisation (`sec:dual`)

Source : `Include/Dualite.tex`, fin du chapitre `sec:dual` (lignes 546–631). L'en-tête de
sous-section « Compacité faible et optimisation » (`subsec:CompaciteConvexes`) y est mis en
commentaire : ces énoncés appartiennent donc formellement à la sous-section
`subsec:HahnBanachGeom` ; on cite ici le label du chapitre.

Les objets du cours sont ceux de Mathlib : topologie faible = `WeakSpace ℝ E` (l'image
`toWeakSpace ℝ E '' C` est la partie `C` vue dans `E` muni de la topologie faible). L'ensemble
polaire du cours (`φ(x) ≤ 1`, unilatéral) diffère de `StrongDual.polar` de Mathlib
(`‖φ(x)‖ ≤ 1`) ; il est introduit fidèlement (`M1Analyse.polaire`) et relié à Mathlib pour les
parties symétriques.
-/

open Set Topology Filter Metric NormedSpace

namespace M1Analyse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- L'ensemble polaire `C° := {φ ∈ E^* | ∀ x ∈ C, φ(x) ≤ 1}` d'une partie `C` d'un evn
(`def:convexePolaire`). -/
def polaire (C : Set E) : Set (StrongDual ℝ E) :=
  {φ | ∀ x ∈ C, φ x ≤ 1}

/-- **Déf. `def:convexePolaire` (Ensemble polaire), lien avec Mathlib.** Pour une partie `C`
symétrique (`x ∈ C ⇒ -x ∈ C`), l'ensemble polaire du cours coïncide avec le polaire (absolu)
`StrongDual.polar ℝ C` de Mathlib. -/
theorem def_convexePolaire_eq_polar (C : Set E) (hC : ∀ x ∈ C, -x ∈ C) :
    polaire C = StrongDual.polar ℝ C := by
  ext φ
  simp only [polaire, mem_ofPred_eq, StrongDual.polar, LinearMap.polar_mem_iff,
    LinearMap.flip_apply, topDualPairing_apply, Real.norm_eq_abs, abs_le]
  constructor
  · intro h x hx
    refine ⟨?_, h x hx⟩
    have := h (-x) (hC x hx)
    rw [map_neg] at this
    linarith
  · intro h x hx
    exact (h x hx).2

/-- **Prop. `prop:cvxFaibleFerme` (Dualité polaire).** Pour tout convexe fermé `C` contenant `0`
d'un evn `E`, on a `C = {x ∈ E | ∀ φ ∈ C°, φ(x) ≤ 1}`. -/
theorem prop_cvxFaibleFerme (C : Set E) (hC : Convex ℝ C) (hCf : IsClosed C) (h0 : (0 : E) ∈ C) :
    C = {x | ∀ φ ∈ polaire C, φ x ≤ 1} := by
  refine Subset.antisymm (fun x hx φ hφ => hφ x hx) fun x hx => ?_
  by_contra hxC
  obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hC hCf hxC
  have hu : 0 < u := by simpa using hfC 0 h0
  have hmem : u⁻¹ • f ∈ polaire C := fun y hy => by
    change u⁻¹ * f y ≤ 1
    rw [inv_mul_le_one₀ hu]
    exact (hfC y hy).le
  have := hx _ hmem
  change u⁻¹ * f x ≤ 1 at this
  rw [inv_mul_le_one₀ hu] at this
  linarith

/-- **Cor. `corol:cvxFermeBdComp`, premier point.** Tout convexe fermé `C` d'un evn `E` est
faiblement fermé. -/
theorem corol_cvxFermeBdComp_ferme (C : Set E) (hC : Convex ℝ C) (hCf : IsClosed C) :
    IsClosed (toWeakSpace ℝ E '' C) := by
  have := hC.toWeakSpace_closure (𝕜 := ℝ)
  rw [hCf.closure_eq] at this
  rw [this]
  exact isClosed_closure

/-- **Cor. `corol:cvxFermeBdComp`, second point.** Si de plus `C` est borné et `E` est réflexif,
alors `C` est faiblement compact. -/
theorem corol_cvxFermeBdComp (hE : Reflexif E) (C : Set E) (hC : Convex ℝ C) (hCf : IsClosed C)
    (hCb : Bornology.IsBounded C) : IsCompact (toWeakSpace ℝ E '' C) := by
  have hcl := corol_cvxFermeBdComp_ferme C hC hCf
  rw [← hcl.closure_eq]
  refine isCompact_closure_of_isBounded ℝ E _ ?_ ?_
  · rwa [(toWeakSpace ℝ E).injective.preimage_image]
  · intro y _
    obtain ⟨x, hx⟩ := hE.2 (StrongDual.toWeakDual.symm y)
    refine ⟨toWeakSpace ℝ E x, ?_⟩
    refine DFunLike.ext _ _ fun φ => ?_
    exact DFunLike.congr_fun hx φ

/-- Les ensembles de sous-niveau d'une fonction dont l'épigraphe est convexe sont convexes. -/
theorem convex_sousNiveau {f : E → EReal} (hcvx : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (m : ℝ) :
    Convex ℝ {x | f x ≤ m} := by
  intro x hx y hy a b ha hb hab
  have := hcvx (x := (x, m)) (y := (y, m)) hx hy ha hb hab
  simp only [mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
    smul_eq_mul] at this
  simpa [← add_mul, hab] using this

/-- Une fonction convexe s.c.i. à valeurs dans `]-∞, ∞]` est s.c.i. pour la topologie faible. -/
theorem lowerSemicontinuous_faible {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥)
    (hcvx : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hlsc : LowerSemicontinuous f) :
    LowerSemicontinuous (fun w : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm w)) := by
  refine lowerSemicontinuous_iff_isClosed_preimage.2 fun y => ?_
  have himg : (fun w : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm w)) ⁻¹' Iic y =
      toWeakSpace ℝ E '' {x | f x ≤ y} := by
    ext w
    simp only [mem_preimage, mem_Iic, mem_image, mem_ofPred_eq]
    exact ⟨fun h => ⟨_, h, LinearEquiv.apply_symm_apply _ w⟩,
      fun ⟨x, hx, hxw⟩ => by rw [← hxw, LinearEquiv.symm_apply_apply]; exact hx⟩
  rw [himg]
  induction y using EReal.rec with
  | bot =>
    have : {x | f x ≤ ⊥} = ∅ := eq_empty_iff_forall_notMem.2 fun x hx => hbot x (le_bot_iff.1 hx)
    rw [this, image_empty]
    exact isClosed_empty
  | top => simp
  | coe m =>
    exact corol_cvxFermeBdComp_ferme _ (convex_sousNiveau hcvx m)
      (hlsc.isClosed_preimage (m : EReal))

/-- **Cor. `corol:minFctCvxRefl` (Minimisation par convexité et compacité), premier point.**
Soient `E` un evn réflexif, `f : E → ]-∞, ∞]` convexe s.c.i. et `M ∈ ℝ`. Si `{f ≤ M}` est non
vide et borné, alors `f` admet un minimiseur.
Remarque : la convexité d'une fonction à valeurs dans `]-∞, ∞]` est exprimée par la convexité de
son épigraphe `{(x, t) ∈ E × ℝ | f(x) ≤ t}`. -/
theorem corol_minFctCvxRefl (hE : Reflexif E) {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥)
    (hcvx : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hlsc : LowerSemicontinuous f) (M : ℝ)
    (hne : {x | f x ≤ M}.Nonempty) (hbd : Bornology.IsBounded {x | f x ≤ M}) :
    ∃ x₀, ∀ x, f x₀ ≤ f x := by
  set K := {x | f x ≤ M}
  have hK : IsCompact (toWeakSpace ℝ E '' K) :=
    corol_cvxFermeBdComp hE K (convex_sousNiveau hcvx M) (hlsc.isClosed_preimage (M : EReal)) hbd
  obtain ⟨a, ⟨x₀, hx₀K, rfl⟩, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn (hne.image _) hK
    ((lowerSemicontinuous_faible hbot hcvx hlsc).lowerSemicontinuousOn _)
  refine ⟨x₀, fun x => ?_⟩
  have hmin' : ∀ y ∈ K, f x₀ ≤ f y := fun y hy => by
    have := isMinOn_iff.1 hmin _ (mem_image_of_mem _ hy)
    simp only [LinearEquiv.symm_apply_apply] at this
    exact this
  by_cases hx : x ∈ K
  · exact hmin' x hx
  · have : (M : EReal) < f x := lt_of_not_ge hx
    exact (hx₀K.trans this.le)

/-- **Cor. `corol:minFctCvxRefl`, second point.** Soient `E` un evn réflexif, `f : E → ]-∞, ∞]`
convexe s.c.i., `g : E → ℝ` faiblement continue sur les bornés et `M ∈ ℝ`. Si
`{f + g ≤ M}` est non vide et borné, alors `f + g` admet un minimiseur.
Remarque : « `g` faiblement continue sur les bornés » est formalisé par : pour toute partie bornée
`A ⊆ E`, la restriction de `g` à `A` est continue pour la topologie faible ; la convexité de `f`
est exprimée par celle de son épigraphe. -/
theorem corol_minFctCvxRefl_perturbation (hE : Reflexif E) {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥)
    (hcvx : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2}) (hlsc : LowerSemicontinuous f) (g : E → ℝ)
    (hg : ∀ A : Set E, Bornology.IsBounded A →
      ContinuousOn (fun w : WeakSpace ℝ E => g ((toWeakSpace ℝ E).symm w)) (toWeakSpace ℝ E '' A))
    (M : ℝ) (hne : {x | f x + g x ≤ M}.Nonempty)
    (hbd : Bornology.IsBounded {x | f x + g x ≤ M}) :
    ∃ x₀, ∀ x, f x₀ + g x₀ ≤ f x + g x := by
  set K := {x | f x + g x ≤ M}
  obtain ⟨R, hR⟩ := hbd.subset_closedBall 0
  set B := closedBall (0 : E) R
  have hB : IsCompact (toWeakSpace ℝ E '' B) :=
    corol_cvxFermeBdComp hE B (convex_closedBall 0 R) isClosed_closedBall isBounded_closedBall
  set h : WeakSpace ℝ E → EReal := fun w =>
    f ((toWeakSpace ℝ E).symm w) + (g ((toWeakSpace ℝ E).symm w) : EReal)
  have hlscB : LowerSemicontinuousOn h (toWeakSpace ℝ E '' B) := by
    refine LowerSemicontinuousOn.add'
      ((lowerSemicontinuous_faible hbot hcvx hlsc).lowerSemicontinuousOn _) ?_
      fun _ _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))
    exact (continuous_coe_real_ereal.comp_continuousOn
      (hg B isBounded_closedBall)).lowerSemicontinuousOn
  obtain ⟨a, ⟨x₀, hx₀B, rfl⟩, hmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn ((hne.mono hR).image _) hB hlscB
  have hmin' : ∀ y ∈ B, f x₀ + g x₀ ≤ f y + g y := fun y hy => by
    have := isMinOn_iff.1 hmin _ (mem_image_of_mem _ hy)
    simp only [h, LinearEquiv.symm_apply_apply] at this
    exact this
  refine ⟨x₀, fun x => ?_⟩
  by_cases hx : x ∈ B
  · exact hmin' x hx
  · obtain ⟨x₁, hx₁⟩ := hne
    have hxK : x ∉ K := fun hxK => hx (hR hxK)
    have : (M : EReal) < f x + g x := lt_of_not_ge hxK
    exact ((hmin' x₁ (hR hx₁)).trans hx₁).trans this.le

end M1Analyse
