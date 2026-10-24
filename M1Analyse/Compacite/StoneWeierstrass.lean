/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.UnitInterval
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Complex.Basic

/-!
# §3.7 Théorème de Stone-Weierstrass (`subsec:StoneWeierstrass`)

Source : `Include/Compacite.tex`, sous-section `subsec:StoneWeierstrass`.

L'espace `C⁰(X, ℝ)` du cours est le type Mathlib `C(X, ℝ)`, muni de la norme uniforme
`‖·‖_∞` (`X` compact). Une algèbre (pas forcément unitaire) de fonctions est une
`NonUnitalSubalgebra`. Le théorème de Stone-Weierstrass de Mathlib
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`) porte sur une
sous-algèbre *unitaire* ; on en déduit la version du cours (algèbre non unitaire ne s'annulant
pas simultanément en un point) en montrant, comme dans le `lem:StoneUnite`, que l'adhérence
contient la fonction constante `1`.

Remarque : dans le cours un compact est par définition séparé ; les énoncés ci-dessous ne
supposent que `[CompactSpace X]` (la séparation n'est pas nécessaire, et découle d'ailleurs de
l'hypothèse de séparation des points par des fonctions continues).

Les lemmes `lem:StoneSqrt`, `corol:StoneMinMax` sont ici déduits du théorème (au lieu d'en être
des étapes de preuve). La `prop:StoneCtrEx` (facultative) n'est pas formalisée.
-/

open Set Topology Filter

namespace M1Analyse

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Étape de la preuve du `lem:StoneUnite` : si `A` ne s'annule pas simultanément en un point,
alors la fonction constante `1` est adhérente à `A`. On construit `f ∈ A` avec `0 < f ≤ 1`, puis
`1 - (1 - f)^N ∈ A` (polynôme en `f` sans terme constant) converge uniformément vers `1`. -/
theorem one_mem_closure_of_forall_ne_zero (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hA : ∀ x : X, ∃ f ∈ A, f x ≠ 0) : (1 : C(X, ℝ)) ∈ closure (A : Set C(X, ℝ)) := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have : (1 : C(X, ℝ)) = 0 := by ext x; exact (IsEmpty.false x).elim
    rw [this]
    exact subset_closure A.zero_mem
  choose F hFA hF using hA
  -- couverture finie de `X` par les ouverts `{F x ≠ 0}`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => {y | F x y ≠ 0})
    (fun x => isOpen_ne_fun (F x).continuous continuous_const)
    (fun y _ => mem_iUnion.2 ⟨y, hF y⟩)
  set f : C(X, ℝ) := ∑ x ∈ t, F x * F x with hf_def
  have hfA : f ∈ A := sum_mem fun x _ => A.mul_mem (hFA x) (hFA x)
  have hfpos : ∀ y, 0 < f y := by
    intro y
    obtain ⟨x, hx, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ y))
    simp only [hf_def, ContinuousMap.coe_sum, ContinuousMap.coe_mul, Finset.sum_apply,
      Pi.mul_apply]
    exact Finset.sum_pos' (fun i _ => mul_self_nonneg _) ⟨x, hx, mul_self_pos.2 hxy⟩
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMinOn univ_nonempty f.continuous.continuousOn
  set c := f y₀
  have hc : 0 < c := hfpos y₀
  set M := ‖f‖
  have hfM : ∀ y, f y ≤ M := fun y => (le_abs_self _).trans (f.norm_coe_le_norm y)
  have hM : 0 < M := hc.trans_le (hfM y₀)
  set g : C(X, ℝ) := M⁻¹ • f
  have hgA : g ∈ A := A.smul_mem _ hfA
  set q := 1 - c / M
  have hq0 : 0 ≤ q := by
    simp only [q, sub_nonneg]; exact (div_le_one hM).2 (hfM y₀)
  have hq1 : q < 1 := by simp only [q]; linarith [div_pos hc hM]
  have hnorm : ‖1 - g‖ ≤ q := by
    rw [ContinuousMap.norm_le _ hq0]
    intro y
    have h1 : c ≤ f y := hy₀ (mem_univ y)
    have h2 : g y = f y / M := by simp [g, div_eq_inv_mul]
    have h3 : f y / M ≤ 1 := (div_le_one hM).2 (hfM y)
    have h4 : c / M ≤ f y / M := div_le_div_of_nonneg_right h1 hM.le
    simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply, h2, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith)]
    linarith
  -- les sommes partielles `1 - (1 - g)^N` sont dans `A`
  have hmem : ∀ N : ℕ, 1 - (1 - g) ^ N ∈ A := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have : 1 - (1 - g) ^ (N + 1) = g + (1 - (1 - g) ^ N) - g * (1 - (1 - g) ^ N) := by ring
      rw [this]
      exact A.sub_mem (A.add_mem hgA ih) (A.mul_mem hgA ih)
  refine mem_closure_of_tendsto (f := fun N : ℕ => 1 - (1 - g) ^ N) (b := atTop) ?_
    (Eventually.of_forall hmem)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  calc ‖1 - (1 - g) ^ N - 1‖ = ‖(1 - g) ^ N‖ := by rw [← norm_neg]; congr 1; ring
    _ ≤ ‖1 - g‖ ^ N := norm_pow_le _ _
    _ ≤ q ^ N := pow_le_pow_left₀ (norm_nonneg _) hnorm N

/-- La sous-algèbre unitaire de `C(X, ℝ)` portée par l'adhérence de `A`, lorsque `1 ∈ Ā`. -/
private def closureSubalgebra (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (h1 : (1 : C(X, ℝ)) ∈ closure (A : Set C(X, ℝ))) : Subalgebra ℝ C(X, ℝ) where
  carrier := closure (A : Set C(X, ℝ))
  mul_mem' ha hb := A.topologicalClosure.mul_mem ha hb
  add_mem' ha hb := A.topologicalClosure.add_mem ha hb
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact A.topologicalClosure.smul_mem r h1

/-- **Thm. `th:StoneWeierstrass` (Stone-Weierstrass).** Soit `X` un espace topologique
compact et `A ⊆ C⁰(X, ℝ)` une algèbre (pas forcément unitaire) qui (i) sépare les points et
(ii) ne s'annule pas simultanément en un point. Alors `Ā = C⁰(X, ℝ)` pour la convergence
uniforme.
Preuve : on ne refait pas la preuve du cours ; on se ramène (via `lem:StoneUnite`, `1 ∈ Ā`) au
théorème de Stone-Weierstrass de Mathlib pour une sous-algèbre unitaire
(`ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints`). La preuve de Mathlib
suit les mêmes étapes que le cours : `|f| ∈ Ā` pour `f ∈ Ā` (`abs_mem_subalgebra_closure`, par
approximation polynomiale de `|·|` sur un segment, là où le cours approche `√·`), puis
`min, max` (`inf_mem_closed_subalgebra`, `sup_mem_closed_subalgebra`), puis un argument de
recouvrement par compacité (`sublattice_closure_eq_top`). -/
theorem th_StoneWeierstrass (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) :
    closure (A : Set C(X, ℝ)) = univ := by
  set S := closureSubalgebra A (one_mem_closure_of_forall_ne_zero A hnv)
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := hsep x y hxy
    exact ⟨f, ⟨f, subset_closure hf, rfl⟩, hfxy⟩
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  have hcl : IsClosed (S : Set C(X, ℝ)) := isClosed_closure
  have h' : (S.topologicalClosure : Set C(X, ℝ)) = univ := by rw [h]; rfl
  rwa [Subalgebra.topologicalClosure_coe, hcl.closure_eq] at h'

/-- **Lemme `lem:StoneUnite`.** Sous les hypothèses du `th:StoneWeierstrass`, `Ā` est une
algèbre unitaire complète : c'est (l'ensemble sous-jacent à) une sous-algèbre unitaire `S` de
`C(X, ℝ)`, complète pour la norme uniforme. -/
theorem lem_StoneUnite (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (_hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) :
    ∃ S : Subalgebra ℝ C(X, ℝ), (S : Set C(X, ℝ)) = closure (A : Set C(X, ℝ)) ∧
      CompleteSpace S :=
  ⟨closureSubalgebra A (one_mem_closure_of_forall_ne_zero A hnv), rfl,
    (isClosed_closure (s := (A : Set C(X, ℝ)))).completeSpace_coe⟩

/-- **Lemme `lem:StoneSqrt`.** Sous les hypothèses du `th:StoneWeierstrass`, soit `f ∈ Ā`.
Si `f ≥ 0` alors `√f ∈ Ā` ; on a toujours `|f| ∈ Ā` ; si `f` ne s'annule pas, `1/f ∈ Ā`.
Remarque : ici déduit directement du `th:StoneWeierstrass` (`Ā = C⁰(X, ℝ)`, toute fonction
continue est dans `Ā`), alors que le cours établit ce lemme comme étape de la preuve ; l'étape
correspondante de la preuve de Mathlib est `abs_mem_subalgebra_closure` (voir
`th_StoneWeierstrass`). L'énoncé est fidèle, mais sa preuve ici ne contient pas l'argument du
cours. -/
theorem lem_StoneSqrt (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) (f : C(X, ℝ)) (_hf : f ∈ closure (A : Set C(X, ℝ))) :
    ((∀ x, 0 ≤ f x) →
        (⟨fun x => √(f x), by fun_prop⟩ : C(X, ℝ)) ∈ closure (A : Set C(X, ℝ))) ∧
      |f| ∈ closure (A : Set C(X, ℝ)) ∧
      ∀ h : ∀ x, f x ≠ 0,
        (⟨fun x => (f x)⁻¹, f.continuous.inv₀ h⟩ : C(X, ℝ)) ∈ closure (A : Set C(X, ℝ)) := by
  simp [th_StoneWeierstrass A hsep hnv]

/-- **Cor. `corol:StoneMinMax`.** Sous les hypothèses du `th:StoneWeierstrass`, si
`f, g ∈ Ā` alors `min {f, g}` et `max {f, g}` appartiennent à `Ā`.
Remarque : comme `lem_StoneSqrt`, déduit directement du `th:StoneWeierstrass` (`Ā = C⁰(X, ℝ)`) ;
l'étape correspondante de la preuve de Mathlib est `inf_mem_closed_subalgebra`,
`sup_mem_closed_subalgebra` (voir `th_StoneWeierstrass`). -/
theorem corol_StoneMinMax (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) (f g : C(X, ℝ))
    (_hf : f ∈ closure (A : Set C(X, ℝ))) (_hg : g ∈ closure (A : Set C(X, ℝ))) :
    f ⊓ g ∈ closure (A : Set C(X, ℝ)) ∧ f ⊔ g ∈ closure (A : Set C(X, ℝ)) := by
  simp [th_StoneWeierstrass A hsep hnv]

/-- **Lemme `lem:StoneDirac`.** Sous les hypothèses du `th:StoneWeierstrass`, pour tout
voisinage ouvert `V` de tout `x ∈ X` et tout `ε > 0`, il existe `f ∈ A` telle que
`0 ≤ f ≤ 1`, `f(x) > 1 - ε` et `f < ε` sur `X ∖ V`. -/
theorem lem_StoneDirac (A : NonUnitalSubalgebra ℝ C(X, ℝ))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) (x : X) (V : Set X) (hV : IsOpen V) (hxV : x ∈ V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f ∈ A, (∀ y, 0 ≤ f y ∧ f y ≤ 1) ∧ 1 - ε < f x ∧ ∀ y ∉ V, f y < ε := by
  -- `X` est séparé, car les fonctions continues de `A` séparent les points
  have : T2Space X := by
    refine T2Space.of_injective_continuous (f := fun y : X => fun g : A => (g : C(X, ℝ)) y)
      ?_ (continuous_pi fun g => (g : C(X, ℝ)).continuous)
    intro y z hyz
    by_contra hne
    obtain ⟨g, hg, hgyz⟩ := hsep y z hne
    exact hgyz (congrFun hyz ⟨g, hg⟩)
  -- fonction d'Urysohn valant `1` en `x` et `0` hors de `V`
  obtain ⟨u, hu0, hu1, hu⟩ := exists_continuous_zero_one_of_isClosed hV.isClosed_compl
    isClosed_singleton (disjoint_singleton_right.2 (not_notMem.2 hxV))
  set δ := min ε 1 with hδ_def
  have hδ0 : 0 < δ := lt_min hε one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  set h : C(X, ℝ) := ContinuousMap.const X (δ / 2) + (1 - δ) • u
  have hcl := th_StoneWeierstrass A hsep hnv
  obtain ⟨f, hfA, hfh⟩ := Metric.mem_closure_iff.1 (hcl ▸ mem_univ h) (δ / 2) (by positivity)
  have hpt : ∀ y, |f y - h y| < δ / 2 := fun y => by
    have := (ContinuousMap.dist_apply_le_dist (f := h) (g := f) y).trans_lt hfh
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hh : ∀ y, h y = δ / 2 + (1 - δ) * u y := fun y => by simp [h]
  refine ⟨f, hfA, fun y => ?_, ?_, fun y hy => ?_⟩
  · have := abs_lt.1 (hpt y)
    have hu' := hu y
    rw [hh] at this
    have : 0 ≤ (1 - δ) * u y := mul_nonneg (by linarith) hu'.1
    have : (1 - δ) * u y ≤ 1 - δ := mul_le_of_le_one_right (by linarith) hu'.2
    constructor <;> linarith
  · have := abs_lt.1 (hpt x)
    rw [hh, hu1 rfl] at this
    simp only [Pi.one_apply, mul_one] at this
    linarith
  · have := abs_lt.1 (hpt y)
    rw [hh, hu0 hy] at this
    simp only [Pi.zero_apply, mul_zero, add_zero] at this
    linarith

/-- La `ℝ`-algèbre `A ∩ C⁰(X, ℝ)` des éléments réels d'une algèbre `A ⊆ C⁰(X, ℂ)`, vue dans
`C(X, ℝ)` (preuve du `corol:StoneComplexe`). -/
private def realPart (A : NonUnitalSubalgebra ℂ C(X, ℂ)) : NonUnitalSubalgebra ℝ C(X, ℝ) where
  carrier := {g | (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp g ∈ A}
  add_mem' {g h} hg hh := by
    have : (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp (g + h) =
        (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp g +
          (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp h := by
      ext x; simp
    change _ ∈ A; rw [this]; exact A.add_mem hg hh
  zero_mem' := by
    have : (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp (0 : C(X, ℝ)) = 0 := by
      ext x; simp
    change _ ∈ A; rw [this]; exact A.zero_mem
  mul_mem' {g h} hg hh := by
    have : (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp (g * h) =
        (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp g *
          (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp h := by
      ext x; simp
    change _ ∈ A; rw [this]; exact A.mul_mem hg hh
  smul_mem' r g hg := by
    have : (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp (r • g) =
        (r : ℂ) • (ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal).comp g := by
      ext x; simp
    change _ ∈ A; rw [this]; exact A.smul_mem (r : ℂ) hg

/-- **Cor. `corol:StoneComplexe` (Stone-Weierstrass complexe).** Soit `X` un espace topologique
compact et `A ⊆ C⁰(X, ℂ)` une algèbre qui (i) sépare les points, (ii) ne s'annule pas
simultanément en un point, (iii) est stable par conjugaison complexe. Alors `Ā = C⁰(X, ℂ)`
pour la convergence uniforme. -/
theorem corol_StoneComplexe (A : NonUnitalSubalgebra ℂ C(X, ℂ))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0)
    (hconj : ∀ f ∈ A, star f ∈ A) :
    closure (A : Set C(X, ℂ)) = univ := by
  set ι : C(ℝ, ℂ) := ContinuousMap.mk Complex.ofReal Complex.continuous_ofReal
  -- parties réelle et imaginaire d'un élément de `A` : éléments de `A ∩ C⁰(X, ℝ)`
  have hre : ∀ f ∈ A, (⟨fun x => (f x).re, by fun_prop⟩ : C(X, ℝ)) ∈ realPart A := by
    intro f hf
    have : ι.comp ⟨fun x => (f x).re, by fun_prop⟩ = (2⁻¹ : ℂ) • (f + star f) := by
      ext x; apply Complex.ext
      · simp [ι]; ring
      · simp [ι]
    change ι.comp _ ∈ A
    rw [this]; exact A.smul_mem _ (A.add_mem hf (hconj f hf))
  have him : ∀ f ∈ A, (⟨fun x => (f x).im, by fun_prop⟩ : C(X, ℝ)) ∈ realPart A := by
    intro f hf
    have : ι.comp ⟨fun x => (f x).im, by fun_prop⟩ = (-Complex.I / 2) • (f - star f) := by
      ext x; apply Complex.ext
      · simp [ι]; ring
      · simp [ι]
    change ι.comp _ ∈ A
    rw [this]; exact A.smul_mem _ (A.sub_mem hf (hconj f hf))
  -- `A ∩ C⁰(X, ℝ)` ne s'annule pas simultanément, donc `1` est adhérent à `A`
  have hnvR : ∀ x : X, ∃ g ∈ realPart A, g x ≠ 0 := by
    intro x
    obtain ⟨f, hf, hfx⟩ := hnv x
    by_cases h : (f x).re = 0
    · refine ⟨_, him f hf, ?_⟩
      intro h'
      exact hfx (Complex.ext h h')
    · exact ⟨_, hre f hf, h⟩
  have h1 : (1 : C(X, ℂ)) ∈ closure (A : Set C(X, ℂ)) := by
    have h1R := one_mem_closure_of_forall_ne_zero (realPart A) hnvR
    have hι : ι.comp (1 : C(X, ℝ)) = 1 := by ext x; simp [ι]
    rw [← hι]
    exact map_mem_closure (ContinuousMap.continuous_postcomp ι) h1R fun g hg => hg
  -- la `*`-sous-algèbre unitaire portée par `Ā`
  let S : StarSubalgebra ℂ C(X, ℂ) :=
    { carrier := closure (A : Set C(X, ℂ))
      mul_mem' := fun ha hb => A.topologicalClosure.mul_mem ha hb
      add_mem' := fun ha hb => A.topologicalClosure.add_mem ha hb
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact A.topologicalClosure.smul_mem r h1
      star_mem' := fun {a} ha => by
        have : MapsTo star (A : Set C(X, ℂ)) A := fun f hf => hconj f hf
        exact map_mem_closure continuous_star ha this }
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨f, hf, hfxy⟩ := hsep x y hxy
    exact ⟨f, ⟨f, subset_closure hf, rfl⟩, hfxy⟩
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  have hcl : IsClosed (S : Set C(X, ℂ)) := isClosed_closure
  have h' : (S.topologicalClosure : Set C(X, ℂ)) = univ := by rw [h]; rfl
  rwa [StarSubalgebra.topologicalClosure_coe, hcl.closure_eq] at h'

/-- **Rem. `rem:polDens` (Application aux fonctions polynomiales), cas réel.** Les fonctions
polynomiales `ℝ[X₁, …, X_d]` (images des polynômes de `MvPolynomial (Fin d) ℝ` évalués en les
fonctions coordonnées) sont denses dans `C⁰([0,1]^d, ℝ)` pour la convergence uniforme. -/
theorem rem_polDens_reel (d : ℕ) :
    closure ((MvPolynomial.aeval (R := ℝ) fun i : Fin d =>
        (⟨fun x : Fin d → unitInterval => (x i : ℝ), by fun_prop⟩ :
          C(Fin d → unitInterval, ℝ))).range : Set C(Fin d → unitInterval, ℝ)) = univ := by
  set coord : Fin d → C(Fin d → unitInterval, ℝ) := fun i => ⟨fun x => (x i : ℝ), by fun_prop⟩
  set A := (MvPolynomial.aeval (R := ℝ) coord).range
  have hA : A.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    refine ⟨coord i, ⟨coord i, ⟨MvPolynomial.X i, by simp⟩, rfl⟩, ?_⟩
    exact fun h => hi (Subtype.ext h)
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hA
  have h' : (A.topologicalClosure : Set C(Fin d → unitInterval, ℝ)) = univ := by rw [h]; rfl
  rwa [Subalgebra.topologicalClosure_coe] at h'

/-- **Rem. `rem:polDens` (Application aux fonctions polynomiales), cas complexe.** Les fonctions
polynomiales `ℂ[X₁, X̄₁, …, X_d, X̄_d]` (polynômes en les coordonnées `zᵢ` et leurs conjuguées
`z̄ᵢ`) sont denses dans `C⁰(B^d, ℂ)`, où `B := B'_ℂ(0,1)` est la boule unité fermée de `ℂ`. -/
theorem rem_polDens_complexe (d : ℕ) :
    closure ((MvPolynomial.aeval (R := ℂ) (Sum.elim
        (fun i : Fin d => (⟨fun x : Fin d → Metric.closedBall (0 : ℂ) 1 => (x i : ℂ),
          by fun_prop⟩ : C(Fin d → Metric.closedBall (0 : ℂ) 1, ℂ)))
        (fun i : Fin d => star (⟨fun x : Fin d → Metric.closedBall (0 : ℂ) 1 => (x i : ℂ),
          by fun_prop⟩ : C(Fin d → Metric.closedBall (0 : ℂ) 1, ℂ))))).range :
        Set C(Fin d → Metric.closedBall (0 : ℂ) 1, ℂ)) = univ := by
  set Y := Fin d → Metric.closedBall (0 : ℂ) 1
  set coord : Fin d → C(Y, ℂ) := fun i => ⟨fun x => (x i : ℂ), by fun_prop⟩
  set S := StarAlgebra.adjoin ℂ (range coord)
  have hrange : (MvPolynomial.aeval (R := ℂ) (Sum.elim coord fun i => star (coord i))).range =
      S.toSubalgebra := by
    rw [← Algebra.adjoin_range_eq_range_aeval, StarAlgebra.adjoin_toSubalgebra,
      Set.Sum.elim_range]
    congr 2
    ext g
    simp only [mem_range, Set.mem_star]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i, by simp⟩
    · rintro ⟨i, hi⟩; exact ⟨i, by rw [hi, star_star]⟩
  have hS : S.SeparatesPoints := by
    intro x y hxy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hxy
    refine ⟨coord i, ⟨coord i, StarAlgebra.subset_adjoin ℂ _ ⟨i, rfl⟩, rfl⟩, ?_⟩
    exact fun h => hi (Subtype.ext h)
  have h := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  have h' : (S.topologicalClosure : Set C(Y, ℂ)) = univ := by rw [h]; rfl
  rw [StarSubalgebra.topologicalClosure_coe] at h'
  change closure (((MvPolynomial.aeval (R := ℂ) (Sum.elim coord fun i => star (coord i))).range :
    Subalgebra ℂ C(Y, ℂ)) : Set C(Y, ℂ)) = univ
  rw [hrange]
  exact h'

end M1Analyse
