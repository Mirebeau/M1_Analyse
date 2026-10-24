/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.MeasureTheory.Function.L2Space

/-!
# §B Espaces Hilbertiens (`sec:Hilbert`)

Source : `Include/Hilbert.tex` (annexe), section `sec:Hilbert`.

Les objets du cours sont ceux de Mathlib : produit scalaire `inner 𝕜 x y = ⟪x, y⟫_𝕜`
(`InnerProductSpace 𝕜 E`, avec `𝕜 = ℝ` ou `ℂ` via `RCLike 𝕜`), Hilbert = espace préhilbertien
`CompleteSpace`, orthogonal `Kᗮ`, projection orthogonale `Submodule.starProjection`,
représentation de Riesz `InnerProductSpace.toDual`, `ℓ²(ℕ, 𝕜)`, bases hilbertiennes
`HilbertBasis`, cône dual `ProperCone.innerDual`.

**Convention de sesquilinéarité.** Le cours prend les formes sesquilinéaires *linéaires à droite
et antilinéaires à gauche* (`def:prehilbert`) ; c'est exactement la convention de Mathlib
(`inner_smul_left : ⟪r • x, y⟫ = conj r * ⟪x, y⟫`). Le reste du chapitre est cohérent avec ce
choix : `φ_x = ⟪x, ·⟫` est linéaire et `x ↦ φ_x` antilinéaire (`th:reprRiesz`) ; le produit
scalaire de `L²` est `∫ conj (f x) * g x` (`ex:l2Hilbert`) ; les coordonnées dans une base
hilbertienne sont `⟪e_n, x⟫` (`th:baseHilbert`). Aucune adaptation n'est donc nécessaire.

La projection `P_K` sur un convexe fermé non vide (`th:projConvexe`), absente de Mathlib en
dehors du cas des sous-espaces, est introduite comme `M1Analyse.projConvexe 𝕜 K`, définie
seulement pour `K : ConvexeFerme H` (partie non vide, fermée, convexe), à partir du théorème
d'existence et d'unicité `th_projConvexe_existsUnique`.
-/

open Set Filter Topology RCLike
open scoped InnerProductSpace ComplexConjugate lp

namespace M1Analyse

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Espace préhilbertien, Cauchy-Schwarz, Hilbert -/

/-- **Déf. `def:prehilbert` (Espace préhilbertien), sens direct.**
Le produit scalaire `⟪·,·⟫_𝕜` de Mathlib est une forme sesquilinéaire (linéaire à droite,
antilinéaire à gauche), symétrique (`⟪x, y⟫ = conj ⟪y, x⟫`), positive (`⟪x, x⟫ ∈ ℝ₊`) et
définie, et la norme est `‖x‖ = √⟪x, x⟫`. -/
theorem def_prehilbert :
    (∀ (x y y' : H) (c : 𝕜), ⟪x, c • y⟫_𝕜 = c * ⟪x, y⟫_𝕜 ∧
      ⟪x, y + y'⟫_𝕜 = ⟪x, y⟫_𝕜 + ⟪x, y'⟫_𝕜) ∧
    (∀ (x x' y : H) (c : 𝕜), ⟪c • x, y⟫_𝕜 = conj c * ⟪x, y⟫_𝕜 ∧
      ⟪x + x', y⟫_𝕜 = ⟪x, y⟫_𝕜 + ⟪x', y⟫_𝕜) ∧
    (∀ x y : H, ⟪x, y⟫_𝕜 = conj ⟪y, x⟫_𝕜) ∧
    (∀ x : H, ∃ r : ℝ, 0 ≤ r ∧ ⟪x, x⟫_𝕜 = r) ∧
    (∀ x : H, x ≠ 0 → ⟪x, x⟫_𝕜 ≠ 0) ∧
    (∀ x : H, ‖x‖ = √(re ⟪x, x⟫_𝕜)) :=
  ⟨fun x y y' c => ⟨inner_smul_right x y c, inner_add_right x y y'⟩,
   fun x x' y c => ⟨inner_smul_left x y c, inner_add_left x x' y⟩,
   fun x y => (inner_conj_symm x y).symm,
   fun x => ⟨‖x‖ ^ 2, sq_nonneg _, by rw [inner_self_eq_norm_sq_to_K]; push_cast; ring⟩,
   fun x hx => inner_self_ne_zero.mpr hx,
   fun x => norm_eq_sqrt_re_inner x⟩

/-- **Déf. `def:prehilbert` (Espace préhilbertien), sens réciproque.**
Sur un `𝕜`-espace vectoriel `F`, toute forme sesquilinéaire (linéaire à droite, antilinéaire à
gauche) symétrique définie positive `φ` est un produit scalaire au sens de Mathlib : elle
définit une structure `InnerProductSpace.Core 𝕜 F` de produit scalaire `φ` (d'où, par
`InnerProductSpace.ofCore`, un espace préhilbertien de norme `‖x‖ = √φ(x,x)`).
La linéarité à droite découle ici de l'antilinéarité à gauche et de la symétrie. -/
theorem def_prehilbert_ofForme {F : Type*} [AddCommGroup F] [Module 𝕜 F] (φ : F → F → 𝕜)
    (_hlin : ∀ (x y y' : F) (c : 𝕜), φ x (c • y) = c * φ x y ∧ φ x (y + y') = φ x y + φ x y')
    (hantilin : ∀ (x x' y : F) (c : 𝕜), φ (c • x) y = conj c * φ x y ∧
      φ (x + x') y = φ x y + φ x' y)
    (hsymm : ∀ x y, φ x y = conj (φ y x))
    (hpos : ∀ x, ∃ r : ℝ, 0 ≤ r ∧ φ x x = r)
    (hdef : ∀ x, x ≠ 0 → φ x x ≠ 0) :
    ∃ c : InnerProductSpace.Core 𝕜 F, ∀ x y, c.inner x y = φ x y :=
  ⟨{ inner := φ
     conj_inner_symm := fun x y => (hsymm x y).symm
     re_inner_nonneg := fun x => by
       obtain ⟨r, hr, hx⟩ := hpos x
       rw [hx, ofReal_re]; exact hr
     add_left := fun x y z => (hantilin x y z 1).2
     smul_left := fun x y r => (hantilin x x y r).1
     definite := fun x hx => by_contra fun h => hdef x h hx }, fun _ _ => rfl⟩

/-- **Identités de `def:prehilbert`.** Développement du carré et identité du parallélogramme :
`‖x+y‖² = ‖x‖² + ‖y‖² + 2 Re⟪x,y⟫` et `‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)`. -/
theorem prehilbert_identites (x y : H) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * re ⟪x, y⟫_𝕜 ∧
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) :=
  ⟨by rw [@norm_add_sq 𝕜]; ring, parallelogram_law_with_norm 𝕜 x y⟩

/-- **Prop. `prop:CauchySchwarz` (Inégalité de Cauchy-Schwarz).**
`|⟪x,y⟫| ≤ ‖x‖ ‖y‖`, avec égalité ssi `x` et `y` sont colinéaires
(colinéarité exprimée par : `x = 0` ou `y = λ x` pour un `λ ∈ 𝕜`). -/
theorem prop_CauchySchwarz (x y : H) :
    ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ ∧
    (‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ c : 𝕜, y = c • x) :=
  ⟨norm_inner_le_norm x y, (norm_inner_eq_norm_tfae 𝕜 x y).out 1 3⟩

/-- **Prop. `prop:CauchySchwarz`, « `‖·‖` définit une norme ».**
Pour un produit scalaire `φ` (au sens de `def:prehilbert`, i.e. une structure
`InnerProductSpace.Core`) sur un `𝕜`-espace vectoriel `F`, l'application `N x = √φ(x,x)`
satisfait les axiomes d'une norme : séparation, homogénéité, inégalité triangulaire. -/
theorem prop_CauchySchwarz_norme {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    (c : InnerProductSpace.Core 𝕜 F) :
    let N : F → ℝ := fun x => √(re (c.inner x x))
    (∀ x, N x = 0 ↔ x = 0) ∧ (∀ (a : 𝕜) x, N (a • x) = ‖a‖ * N x) ∧
      (∀ x y, N (x + y) ≤ N x + N y) := by
  let _ : NormedAddCommGroup F := c.toNormedAddCommGroup
  let _ : InnerProductSpace 𝕜 F := InnerProductSpace.ofCore c.toCore
  exact ⟨fun x => (norm_eq_zero : ‖x‖ = 0 ↔ x = 0), fun a x => (norm_smul a x : ‖a • x‖ = _),
    fun x y => (norm_add_le x y : ‖x + y‖ ≤ _)⟩

/-- **Déf. `def:Hilbert` (Hilbert).** Un Hilbert est un espace préhilbertien complet ; en Lean,
`[InnerProductSpace 𝕜 H] [CompleteSpace H]`. La complétude `CompleteSpace H` équivaut à la
convergence de toute suite de Cauchy. -/
theorem def_Hilbert :
    CompleteSpace H ↔ ∀ u : ℕ → H, CauchySeq u → ∃ l, Tendsto u atTop (𝓝 l) :=
  ⟨fun _ _ hu => cauchySeq_tendsto_of_complete hu, Metric.complete_of_cauchySeq_tendsto⟩

/-! ### Projection sur un convexe fermé -/

/-- **Convexe fermé non vide** (hypothèses de `th:projConvexe`) : une partie `K ⊆ H` non vide,
fermée et convexe. C'est le domaine de définition de la projection `P_K` (`projConvexe`). -/
structure ConvexeFerme (H : Type*) [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] where
  /-- La partie `K ⊆ H`. -/
  carrier : Set H
  nonempty : carrier.Nonempty
  isClosed : IsClosed carrier
  convex : Convex ℝ carrier

instance {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] :
    SetLike (ConvexeFerme H) H where
  coe := ConvexeFerme.carrier
  coe_injective K L h := by cases K; cases L; congr

section ProjAux

/-- Convexité réelle exprimée avec les scalaires réels plongés dans `𝕜`. -/
private def ConvexCoe (𝕜 : Type*) {H : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (K : Set H) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → (a : 𝕜) • x + (b : 𝕜) • y ∈ K

private lemma isMin_iff_iInf {E : Type*} [NormedAddCommGroup E] {K : Set E} {x y : E}
    (hy : y ∈ K) : ‖x - y‖ = ⨅ w : K, ‖x - w‖ ↔ ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖ := by
  have hbdd : BddBelow (range fun w : K => ‖x - w‖) := ⟨0, by rintro _ ⟨w, rfl⟩; positivity⟩
  constructor
  · intro h z hz
    rw [h]; exact ciInf_le hbdd ⟨z, hz⟩
  · intro h
    have : Nonempty K := ⟨⟨y, hy⟩⟩
    exact le_antisymm (le_ciInf fun w => h w w.2) (ciInf_le hbdd ⟨y, hy⟩)

private lemma exists_min_aux [CompleteSpace H] {K : Set H} (hne : K.Nonempty)
    (hcl : IsClosed K) (hc : ConvexCoe 𝕜 K) (x : H) : ∃ y ∈ K, ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖ := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H
  have hconv : Convex ℝ K := fun u hu v hv a b ha hb hab => hc u hu v hv a b ha hb hab
  obtain ⟨y, hyK, hy⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv x
  exact ⟨y, hyK, (isMin_iff_iInf hyK).mp hy⟩

private lemma caract_aux {K : Set H} (hc : ConvexCoe 𝕜 K) {x y : H} (hy : y ∈ K) :
    (∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖) ↔ ∀ z ∈ K, re ⟪x - y, z - y⟫_𝕜 ≤ 0 := by
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal 𝕜 H
  have hconv : Convex ℝ K := fun u hu v hv a b ha hb hab => hc u hu v hv a b ha hb hab
  rw [← isMin_iff_iInf hy]
  exact norm_eq_iInf_iff_real_inner_le_zero hconv hy

/-- Inégalité de « ferme non-expansivité » déduite de deux conditions d'angle obtus. -/
private lemma moyennee_aux {x y p q : H} (hp : re ⟪x - p, q - p⟫_𝕜 ≤ 0)
    (hq : re ⟪y - q, p - q⟫_𝕜 ≤ 0) : ‖p - q‖ ^ 2 ≤ re ⟪x - y, p - q⟫_𝕜 := by
  have h1 : x - y = (x - p) - (y - q) + (p - q) := by abel
  have h2 : re ⟪x - p, p - q⟫_𝕜 = - re ⟪x - p, q - p⟫_𝕜 := by
    rw [show p - q = -(q - p) by abel, inner_neg_right, map_neg]
  rw [h1, inner_add_left, inner_sub_left, map_add, map_sub, h2, @inner_self_eq_norm_sq 𝕜]
  linarith

end ProjAux

section Projection

variable [Module ℝ H] [IsScalarTower ℝ 𝕜 H]

private lemma convexCoe_of_convex {K : Set H} (h : Convex ℝ K) : ConvexCoe 𝕜 K := by
  intro x hx y hy a b ha hb hab
  have := h hx hy ha hb hab
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜)] at this

variable [CompleteSpace H]

include 𝕜 in
/-- **Thm. `th:projConvexe` (Projection sur un convexe fermé), existence et unicité.**
Soit `H` Hilbert et `K ⊆ H` convexe fermé non vide. Pour tout `x ∈ H`, le problème
`argmin_{y ∈ K} ‖x - y‖` admet une unique solution. -/
theorem th_projConvexe_existsUnique {K : Set H} (hne : K.Nonempty) (hcl : IsClosed K)
    (hconv : Convex ℝ K) (x : H) : ∃! y, y ∈ K ∧ ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖ := by
  have hc := convexCoe_of_convex (𝕜 := 𝕜) hconv
  obtain ⟨y, hyK, hy⟩ := exists_min_aux hne hcl hc x
  refine ⟨y, ⟨hyK, hy⟩, fun y' ⟨hy'K, hy'⟩ => ?_⟩
  have a := (caract_aux hc hyK).mp hy
  have b := (caract_aux hc hy'K).mp hy'
  have := moyennee_aux (a y' hy'K) (b y hyK)
  rw [sub_self, inner_zero_left, map_zero] at this
  exact (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp
    (le_antisymm this (sq_nonneg _)) |> norm_eq_zero.mp)).symm

variable (𝕜) in
/-- **Projection `P_K` de `th:projConvexe`.** Pour `H` un `𝕜`-Hilbert et `K ⊆ H` convexe fermé
non vide, `P_K(x) := projConvexe 𝕜 K x` est l'unique minimiseur de `y ↦ ‖x - y‖` sur `K`
(`th_projConvexe_existsUnique`) ; caractérisation : `th_projConvexe`, `eq_projConvexe_of_isMin`.
(Le corps `𝕜` ne sert qu'à invoquer le théorème ; la valeur n'en dépend pas, puisque le
minimiseur est défini par la seule norme.)
Lien avec Mathlib : pour un sous-espace fermé, `P_K` est `Submodule.starProjection`
(`projConvexe_eq_starProjection`) ; Mathlib n'a pas de projection sur un convexe général. -/
noncomputable def projConvexe (K : ConvexeFerme H) (x : H) : H :=
  (th_projConvexe_existsUnique (𝕜 := 𝕜) K.nonempty K.isClosed K.convex x).exists.choose

/-- **Thm. `th:projConvexe`, définition de `P_K`.** `P_K(x)` appartient à `K` et minimise
`y ↦ ‖x - y‖` sur `K`. -/
theorem th_projConvexe (K : ConvexeFerme H) (x : H) :
    projConvexe 𝕜 K x ∈ K ∧ ∀ z ∈ K, ‖x - projConvexe 𝕜 K x‖ ≤ ‖x - z‖ :=
  (th_projConvexe_existsUnique (𝕜 := 𝕜) K.nonempty K.isClosed K.convex x).exists.choose_spec

/-- **Thm. `th:projConvexe`, unicité.** Tout minimiseur de `y ↦ ‖x - y‖` sur `K` est `P_K(x)`. -/
theorem eq_projConvexe_of_isMin (K : ConvexeFerme H) {x y : H} (hy : y ∈ K)
    (hmin : ∀ z ∈ K, ‖x - y‖ ≤ ‖x - z‖) : y = projConvexe 𝕜 K x :=
  (th_projConvexe_existsUnique (𝕜 := 𝕜) K.nonempty K.isClosed K.convex x).unique ⟨hy, hmin⟩
    (th_projConvexe K x)

/-- **Thm. `th:projConvexe`, condition d'angle obtus (`eq:proj_obtus`).**
`P_K(x)` est caractérisé par : pour tout `y ∈ K`, `Re⟪x - P_K(x), y - P_K(x)⟫ ≤ 0`. -/
theorem th_projConvexe_caract (K : ConvexeFerme H) {x p : H} (hp : p ∈ K) :
    p = projConvexe 𝕜 K x ↔ ∀ y ∈ K, re ⟪x - p, y - p⟫_𝕜 ≤ 0 := by
  have hc := convexCoe_of_convex (𝕜 := 𝕜) K.convex
  refine (?_ : _ ↔ ∀ z ∈ (K : Set H), ‖x - p‖ ≤ ‖x - z‖).trans (caract_aux hc hp)
  refine ⟨fun h => ?_, eq_projConvexe_of_isMin K hp⟩
  rw [h]; exact (th_projConvexe K x).2

/-- **Thm. `th:projConvexe`, opérateur moyenné (`eq:proj_moyennee`).**
Pour tous `x, y ∈ H`, `‖P_K(x) - P_K(y)‖² ≤ Re⟪x - y, P_K(x) - P_K(y)⟫`. -/
theorem th_projConvexe_moyennee (K : ConvexeFerme H) (x y : H) :
    ‖projConvexe 𝕜 K x - projConvexe 𝕜 K y‖ ^ 2 ≤
      re ⟪x - y, projConvexe 𝕜 K x - projConvexe 𝕜 K y⟫_𝕜 := by
  have hx := th_projConvexe (𝕜 := 𝕜) K x
  have hy := th_projConvexe (𝕜 := 𝕜) K y
  exact moyennee_aux ((th_projConvexe_caract (𝕜 := 𝕜) K hx.1).mp rfl _ hy.1)
    ((th_projConvexe_caract (𝕜 := 𝕜) K hy.1).mp rfl _ hx.1)

/-- **Thm. `th:projConvexe`, Lipschitz.** `P_K` est `1`-Lipschitz. -/
theorem th_projConvexe_lipschitz (K : ConvexeFerme H) : LipschitzWith 1 (projConvexe 𝕜 K) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
  have h := th_projConvexe_moyennee (𝕜 := 𝕜) K x y
  have h' := re_inner_le_norm (𝕜 := 𝕜) (x - y) (projConvexe 𝕜 K x - projConvexe 𝕜 K y)
  nlinarith [norm_nonneg (projConvexe 𝕜 K x - projConvexe 𝕜 K y), norm_nonneg (x - y)]

end Projection

/-- **Remarque suivant `th:projConvexe` (opérateur moyenné).** Pour une application
`P : H → H` quelconque, la propriété `eq:proj_moyennee` équivaut à la `1`-lipschitzianité de
`Q := 2P - Id`. -/
theorem projConvexe_moyennee_iff (P : H → H) :
    (∀ x y, ‖P x - P y‖ ^ 2 ≤ re ⟪x - y, P x - P y⟫_𝕜) ↔
      LipschitzWith 1 (fun x => (2 : 𝕜) • P x - x) := by
  have key : ∀ x y, ‖((2 : 𝕜) • P x - x) - ((2 : 𝕜) • P y - y)‖ ^ 2 =
      4 * ‖P x - P y‖ ^ 2 - 4 * re ⟪x - y, P x - P y⟫_𝕜 + ‖x - y‖ ^ 2 := by
    intro x y
    have : ((2 : 𝕜) • P x - x) - ((2 : 𝕜) • P y - y) = (2 : 𝕜) • (P x - P y) - (x - y) := by
      rw [smul_sub]; abel
    rw [this, @norm_sub_sq 𝕜, norm_smul, inner_smul_left, map_ofNat, RCLike.norm_ofNat,
      show (2 : 𝕜) = ((2 : ℝ) : 𝕜) by norm_cast, RCLike.re_ofReal_mul,
      inner_re_symm (𝕜 := 𝕜) (P x - P y)]
    ring
  constructor
  · intro h
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    have h1 := key x y
    have h2 := h x y
    nlinarith [norm_nonneg (((2 : 𝕜) • P x - x) - ((2 : 𝕜) • P y - y)), norm_nonneg (x - y)]
  · intro h x y
    have h1 := h.dist_le_mul x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    linarith [key x y]


/-! ### Représentation de Riesz, exemple `L²` -/

/-- **Thm. `th:reprRiesz` (Représentation de Riesz).** Soit `H` Hilbert. L'application
`x ↦ φ_x := ⟪x, ·⟫` (`innerSL 𝕜`) de `H` dans son dual `H* = StrongDual 𝕜 H` est une bijection
isométrique antilinéaire. (Mathlib : `InnerProductSpace.toDual`.) -/
theorem th_reprRiesz [CompleteSpace H] :
    (∀ x y : H, innerSL 𝕜 x y = ⟪x, y⟫_𝕜) ∧
    Function.Bijective (innerSL 𝕜 : H → StrongDual 𝕜 H) ∧
    (∀ x : H, ‖innerSL 𝕜 x‖ = ‖x‖) ∧
    (∀ x y : H, innerSL 𝕜 (x + y) = innerSL 𝕜 x + innerSL 𝕜 y) ∧
    (∀ (c : 𝕜) (x : H), innerSL 𝕜 (c • x) = conj c • innerSL 𝕜 x) := by
  have h : (innerSL 𝕜 : H → StrongDual 𝕜 H) = InnerProductSpace.toDual 𝕜 H :=
    funext fun x => ContinuousLinearMap.ext fun y => rfl
  refine ⟨fun x y => rfl, h ▸ (InnerProductSpace.toDual 𝕜 H).bijective, innerSL_apply_norm 𝕜,
    fun x y => map_add _ x y, fun c x => (innerSL 𝕜).map_smulₛₗ c x⟩

/-- **Exemple `ex:l2Hilbert` (Hilbert `L²(X, μ)`).** `L²(X, μ)` est un Hilbert, de produit
scalaire `⟪f, g⟫ = ∫ conj (f x) * g x dμ`, et toute forme linéaire continue s'y écrit
`g ↦ ∫ conj (f x) * g x dμ` pour un certain `f ∈ L²(X, μ)`. -/
theorem ex_l2Hilbert {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) :
    CompleteSpace (MeasureTheory.Lp 𝕜 2 μ) ∧
    (∀ f g : MeasureTheory.Lp 𝕜 2 μ, ⟪f, g⟫_𝕜 = ∫ x, conj (f x) * g x ∂μ) ∧
    (∀ φ : StrongDual 𝕜 (MeasureTheory.Lp 𝕜 2 μ), ∃ f : MeasureTheory.Lp 𝕜 2 μ,
      ∀ g, φ g = ∫ x, conj (f x) * g x ∂μ) := by
  have hinner : ∀ f g : MeasureTheory.Lp 𝕜 2 μ, ⟪f, g⟫_𝕜 = ∫ x, conj (f x) * g x ∂μ := by
    intro f g
    rw [MeasureTheory.L2.inner_def]
    simp only [RCLike.inner_apply, mul_comm]
  refine ⟨inferInstance, hinner, fun φ => ⟨(InnerProductSpace.toDual 𝕜 _).symm φ, fun g => ?_⟩⟩
  rw [← hinner, InnerProductSpace.toDual_symm_apply]

/-! ### Décomposition orthogonale -/

/-- **Prop. `prop:decompOrth`, orthogonal.** `F^⊥ := {y ∈ H | ∀ x ∈ F, ⟪x, y⟫ = 0}` est
l'orthogonal `Fᗮ` de Mathlib. -/
theorem prop_decompOrth_orthogonal (F : Submodule 𝕜 H) :
    (Fᗮ : Set H) = {y | ∀ x ∈ F, ⟪x, y⟫_𝕜 = 0} := by
  ext y; exact Submodule.mem_orthogonal F y

section DecompOrth

variable [Module ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- Un sous-espace vectoriel fermé `F ⊆ H` est un convexe fermé non vide. -/
def ConvexeFerme.ofSubmodule (F : Submodule 𝕜 H) (hF : IsClosed (F : Set H)) :
    ConvexeFerme H where
  carrier := F
  nonempty := ⟨0, F.zero_mem⟩
  isClosed := hF
  convex := (F.restrictScalars ℝ).convex

variable [CompleteSpace H]

/-- Pont avec Mathlib : pour un sous-espace fermé `F`, la projection du cours `P_F` est la
projection orthogonale `Submodule.starProjection` de Mathlib. -/
theorem projConvexe_eq_starProjection (F : Submodule 𝕜 H) (hF : IsClosed (F : Set H))
    [F.HasOrthogonalProjection] (x : H) :
    projConvexe 𝕜 (ConvexeFerme.ofSubmodule F hF) x = F.starProjection x :=
  (eq_projConvexe_of_isMin (ConvexeFerme.ofSubmodule F hF) (F.starProjection_apply_mem x)
    ((isMin_iff_iInf (F.starProjection_apply_mem x)).mp (Submodule.starProjection_minimal x))).symm

/-- **Prop. `prop:decompOrth` (Décomposition orthogonale).** Soit `H` Hilbert et `F ⊆ H` un
sous-espace vectoriel fermé. La projection `P_F` est caractérisée par `⟪x - P_F(x), y⟫ = 0`
pour tout `y ∈ F` ; de plus `F ⊕ F^⊥ = H`, `P_F + P_{F^⊥} = Id`, et `P_F`, `P_{F^⊥}` sont
linéaires continues. -/
theorem prop_decompOrth (F : Submodule 𝕜 H) (hF : IsClosed (F : Set H)) :
    let PF := projConvexe 𝕜 (ConvexeFerme.ofSubmodule F hF)
    let PFo := projConvexe 𝕜 (ConvexeFerme.ofSubmodule Fᗮ F.isClosed_orthogonal)
    (∀ x p : H, p ∈ F → (p = PF x ↔ ∀ y ∈ F, ⟪x - p, y⟫_𝕜 = 0)) ∧
    IsCompl F Fᗮ ∧ (∀ x, PF x + PFo x = x) ∧
    (∃ L : H →L[𝕜] H, ⇑L = PF) ∧ (∃ L : H →L[𝕜] H, ⇑L = PFo) := by
  intro PF PFo
  have : CompleteSpace F := hF.isComplete.completeSpace_coe
  have hPF : ∀ x, PF x = F.starProjection x := projConvexe_eq_starProjection F hF
  have hPFo : ∀ x, PFo x = Fᗮ.starProjection x :=
    projConvexe_eq_starProjection Fᗮ F.isClosed_orthogonal
  refine ⟨fun x p hp => ?_, F.isCompl_orthogonal, fun x => ?_,
    ⟨F.starProjection, funext fun x => (hPF x).symm⟩,
    ⟨Fᗮ.starProjection, funext fun x => (hPFo x).symm⟩⟩
  · rw [hPF]
    constructor
    · rintro rfl y hy
      exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal F _).mp
        (Submodule.sub_starProjection_mem_orthogonal x) y hy)
    · exact fun h => (Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp h).symm
  · rw [hPF, hPFo]
    exact Submodule.starProjection_add_starProjection_orthogonal x

end DecompOrth


/-! ### Décomposition associée à un cône (facultatif) -/

section Cone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Cône polaire de `prop:decompCone`.** `K° := {y ∈ H | ∀ x ∈ K, ⟪x, y⟫ ≤ 0}`.
Lien avec Mathlib : le cône dual `ProperCone.innerDual K = {y | ∀ x ∈ K, 0 ≤ ⟪x, y⟫}` de
Mathlib a la convention de signe opposée : `K° = -K*` (`conePolaire_eq_neg_innerDual`). -/
def conePolaire (K : Set E) : Set E := {y | ∀ x ∈ K, ⟪x, y⟫_ℝ ≤ 0}

/-- Le cône polaire `K°` est un convexe fermé non vide (il contient `0`). -/
def ConvexeFerme.conePolaire (K : Set E) : ConvexeFerme E where
  carrier := M1Analyse.conePolaire K
  nonempty := ⟨0, fun x _ => by simp⟩
  isClosed := by
    have : M1Analyse.conePolaire K = ⋂ x ∈ K, {y | ⟪x, y⟫_ℝ ≤ 0} := by
      ext; simp [M1Analyse.conePolaire]
    rw [this]
    exact isClosed_biInter fun x _ =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  convex := by
    intro y₁ h₁ y₂ h₂ a b ha hb _ x hx
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    nlinarith [h₁ x hx, h₂ x hx]

@[simp] lemma ConvexeFerme.coe_conePolaire (K : Set E) :
    (ConvexeFerme.conePolaire K : Set E) = M1Analyse.conePolaire K := rfl

variable [CompleteSpace E]

/-- Pont avec Mathlib : `K° = -K*`, où `K* = ProperCone.innerDual K` est le cône dual
(cf. `ex:coneSdp`). -/
theorem conePolaire_eq_neg_innerDual (K : Set E) :
    conePolaire K = -(ProperCone.innerDual K : Set E) := by
  ext y
  simp [conePolaire]

private lemma decompCone_aux (K : ConvexeFerme E)
    {x y z : E} (hy : y ∈ K) (hz : z ∈ conePolaire K) (hyz : ⟪y, z⟫_ℝ = 0) (hx : x = y + z) :
    y = projConvexe ℝ K x ∧ z = projConvexe ℝ (ConvexeFerme.conePolaire K) x := by
  subst hx
  constructor
  · refine (th_projConvexe_caract K hy).mpr fun y' hy' => ?_
    rw [add_sub_cancel_left, RCLike.re_to_real, inner_sub_right, real_inner_comm y' z,
      real_inner_comm y z, hyz, sub_zero]
    exact hz y' hy'
  · refine (th_projConvexe_caract (ConvexeFerme.conePolaire (K : Set E)) (x := y + z) hz).mpr
      fun z' hz' => ?_
    rw [add_sub_cancel_right, RCLike.re_to_real, inner_sub_right, hyz, sub_zero]
    exact hz' y hy

/-- **Prop. `prop:decompCone` (Décomposition orthogonale associée à un cône).**
Soit `H` un `ℝ`-Hilbert, `K ⊆ H` un cône convexe fermé (`λx + μy ∈ K` pour `x, y ∈ K`,
`λ, μ ≥ 0`) et `K°` son cône polaire. Alors `y = P_K(x)` et `z = P_{K°}(x)` ssi
`y ∈ K`, `z ∈ K°`, `⟪y, z⟫ = 0` et `x = y + z`.
Remarque : `K` est supposé non vide (`K : ConvexeFerme E`), hypothèse implicite dans le cours :
la partie vide satisfait la définition de cône convexe donnée, mais la projection sur `∅` n'est
pas définie. -/
theorem prop_decompCone (K : ConvexeFerme E)
    (hcone : ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a • x + b • y ∈ K) (x y z : E) :
    (y = projConvexe ℝ K x ∧ z = projConvexe ℝ (ConvexeFerme.conePolaire K) x) ↔
      (y ∈ K ∧ z ∈ conePolaire K ∧ ⟪y, z⟫_ℝ = 0 ∧ x = y + z) := by
  refine ⟨?_, fun ⟨hy, hz, hyz, hx⟩ => decompCone_aux K hy hz hyz hx⟩
  rintro ⟨rfl, rfl⟩
  set p := projConvexe ℝ K x
  have hp : p ∈ K := (th_projConvexe K x).1
  have hc := (th_projConvexe_caract K hp).mp rfl
  simp only [RCLike.re_to_real] at hc
  have h0 : (0 : E) ∈ K := by
    obtain ⟨a, ha⟩ := K.nonempty
    simpa using hcone a ha a ha 0 0 le_rfl le_rfl
  have hw : x - p ∈ conePolaire K := by
    intro y' hy'
    have := hc (p + y') (by simpa using hcone p hp y' hy' 1 1 zero_le_one zero_le_one)
    rwa [add_sub_cancel_left, real_inner_comm] at this
  have hpw : ⟪p, x - p⟫_ℝ = 0 := by
    have h1 := hc 0 h0
    have h2 := hc (p + p) (by simpa using hcone p hp p hp 1 1 zero_le_one zero_le_one)
    rw [zero_sub, inner_neg_right] at h1
    rw [add_sub_cancel_left] at h2
    rw [real_inner_comm]; linarith
  have := decompCone_aux K hp hw hpw (add_sub_cancel p x).symm
  exact ⟨hp, this.2 ▸ hw, this.2 ▸ hpw, (this.2 ▸ (add_sub_cancel p x).symm)⟩

/-- **Ex. `ex:coneSdp` (Cône dual de `ℝ₊^d`), auto-dualité.** Le cône `ℝ₊^d ⊆ ℝ^d` est
auto-dual : `K* = K`, où `K* = {y | ∀ x ∈ K, ⟪x, y⟫ ≥ 0}` est `ProperCone.innerDual K`. -/
theorem ex_coneSdp_autoDual (d : ℕ) :
    (ProperCone.innerDual {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i} :
      Set (EuclideanSpace ℝ (Fin d))) = {x | ∀ i, 0 ≤ x i} := by
  ext y
  simp only [SetLike.mem_coe, ProperCone.mem_innerDual, Set.mem_ofPred_eq]
  constructor
  · intro h i
    have := h (x := EuclideanSpace.single i 1) (fun j => by
      by_cases hj : j = i <;> simp [hj])
    simpa [EuclideanSpace.inner_single_left] using this
  · intro hy x hx
    rw [PiLp.inner_apply]
    exact Finset.sum_nonneg fun i _ => by simpa using mul_nonneg (hy i) (hx i)

/-- Le cône `ℝ₊^d = {x ∈ ℝ^d | ∀ i, x_i ≥ 0}` (`ex:coneSdp`), convexe fermé non vide. -/
def orthantPositif (d : ℕ) : ConvexeFerme (EuclideanSpace ℝ (Fin d)) where
  carrier := {x | ∀ i, 0 ≤ x i}
  nonempty := ⟨0, fun i => by simp⟩
  isClosed := by
    have : {x : EuclideanSpace ℝ (Fin d) | ∀ i, 0 ≤ x i} =
        ⋂ i, {x : EuclideanSpace ℝ (Fin d) | 0 ≤ x i} := by ext; simp
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const ((PiLp.continuous_apply 2 _ i).comp continuous_id)
  convex := fun u hu v hv a b ha hb _ i => by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i))

/-- **Ex. `ex:coneSdp`, décomposition associée à `ℝ₊^d`.** Pour `K = ℝ₊^d`, la décomposition
de `prop:decompCone` est `x = x⁺ - x⁻` : `P_K(x) = x⁺` et `P_{K°}(x) = -x⁻`, où
`x⁺_i = max{x_i, 0}` et `x⁻_i = max{-x_i, 0}`. -/
theorem ex_coneSdp_partiesPosNeg (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    let K := orthantPositif d
    let xp : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => max (x i) 0
    let xm : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 fun i => max (-x i) 0
    x = xp - xm ∧ projConvexe ℝ K x = xp ∧
      projConvexe ℝ (ConvexeFerme.conePolaire K) x = -xm := by
  intro K xp xm
  have hx : x = xp - xm := by
    ext i; simp [xp, xm]
  have hcone : ∀ u ∈ K, ∀ v ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a • u + b • v ∈ K :=
    fun u hu v hv a b ha hb i => by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hu i)) (mul_nonneg hb (hv i))
  have h := (prop_decompCone K hcone x xp (-xm)).mpr ⟨fun i => by simp [xp], ?_, ?_, ?_⟩
  · exact ⟨hx, h.1.symm, h.2.symm⟩
  · intro k hk
    rw [PiLp.inner_apply]
    exact Finset.sum_nonpos fun i _ => by
      simpa [xm] using mul_nonneg (le_max_right (-x i) 0) (hk i)
  · rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases le_total 0 (x i) with h | h <;> simp [xp, xm, h]
  · rw [← sub_eq_add_neg]; exact hx

end Cone

/-! ### Hilbert et bases hilbertiennes -/

/-- **Thm. `th:baseHilbert` (Base Hilbertienne).** Pour `H` Hilbert, sont équivalents :
(i) `H` est séparable et de dimension infinie ;
(ii) `H` admet une base hilbertienne `(e_n)_{n ∈ ℕ}` : famille orthonormale (vecteurs unitaires
deux à deux orthogonaux) d'espace engendré dense ;
(iii) il existe une bijection linéaire isométrique entre `H` et `ℓ² = ℓ²(ℕ, 𝕜)`.
Remarque : `ℓ²(ℕ, 𝕜)` est ici l'espace Mathlib `lp (fun _ : ℕ => 𝕜) 2` des suites de carré
sommable, i.e. `L²(ℕ, 𝕜)` pour la mesure de comptage. -/
theorem th_baseHilbert [CompleteSpace H] :
    [TopologicalSpace.SeparableSpace H ∧ ¬ FiniteDimensional 𝕜 H,
      ∃ e : ℕ → H, Orthonormal 𝕜 e ∧ Dense (Submodule.span 𝕜 (range e) : Set H),
      Nonempty (H ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜))].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨hsep, hinf⟩
    obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 H
    have hdist : ∀ i j : w, i ≠ j → 1 ≤ dist (b i) (b j) := by
      intro i j hij
      have h2 : ‖b i - b j‖ ^ 2 = 2 := by
        rw [@norm_sub_sq 𝕜, b.orthonormal.1 i, b.orthonormal.1 j, b.orthonormal.2 hij]
        norm_num
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (b i - b j)]
    have : Countable w := Pairwise.countable_of_isOpen_disjoint
      (s := fun i => Metric.ball (b i) (1 / 2))
      (fun i j hij => Metric.ball_disjoint_ball (by linarith [hdist i j hij]))
      (fun _ => Metric.isOpen_ball) (fun _ => Metric.nonempty_ball.2 (by norm_num))
    have : Infinite w := by
      by_contra hfin
      rw [not_infinite_iff_finite] at hfin
      apply hinf
      let S := Submodule.span 𝕜 (range b)
      have : FiniteDimensional 𝕜 S := FiniteDimensional.span_of_finite 𝕜 (Set.finite_range b)
      have hS : S = ⊤ := by
        rw [← b.dense_span]
        exact (IsClosed.submodule_topologicalClosure_eq
          (Submodule.closed_of_finiteDimensional S)).symm
      exact Module.finite_def.2 (hS ▸ Submodule.fg_span (Set.finite_range b))
    have : Encodable w := Encodable.ofCountable w
    let σ : w ≃ ℕ := @Denumerable.eqv w (Denumerable.ofEncodableOfInfinite w)
    refine ⟨fun n => b (σ.symm n), b.orthonormal.comp _ σ.symm.injective, ?_⟩
    have : range (fun n => b (σ.symm n)) = range b := σ.symm.surjective.range_comp b
    rw [this, Submodule.dense_iff_topologicalClosure_eq_top]
    exact b.dense_span
  tfae_have 2 → 3 := by
    rintro ⟨e, he, hd⟩
    exact ⟨(HilbertBasis.mk he (Submodule.dense_iff_topologicalClosure_eq_top.1 hd).ge).repr⟩
  tfae_have 3 → 2 := by
    rintro ⟨U⟩
    let b : HilbertBasis ℕ 𝕜 H := HilbertBasis.ofRepr U
    exact ⟨b, b.orthonormal, Submodule.dense_iff_topologicalClosure_eq_top.2 b.dense_span⟩
  tfae_have 2 → 1 := by
    rintro ⟨e, he, hd⟩
    refine ⟨?_, fun hfin => ?_⟩
    swap
    · have := he.linearIndependent.finite
      exact not_finite ℕ
    obtain ⟨c, hc, hsc⟩ := (countable_range e).isSeparable.span (R := 𝕜)
    exact ⟨⟨c, hc, (hd.mono hsc).of_closure⟩⟩
  tfae_finish

/-- **Thm. `th:baseHilbert`, formules.** Si `(e_n)` est une base hilbertienne (au sens (ii)),
la bijection de (iii) est `x ↦ (⟪e_n, x⟫)_{n ∈ ℕ}`, de réciproque `(x_n) ↦ ∑ x_n e_n`. -/
theorem th_baseHilbert_repr [CompleteSpace H] (e : ℕ → H) (he : Orthonormal 𝕜 e)
    (hd : Dense (Submodule.span 𝕜 (range e) : Set H)) :
    ∃ U : H ≃ₗᵢ[𝕜] ℓ²(ℕ, 𝕜), (∀ x n, U x n = ⟪e n, x⟫_𝕜) ∧
      ∀ c : ℓ²(ℕ, 𝕜), HasSum (fun n => c n • e n) (U.symm c) := by
  let b := HilbertBasis.mk he (Submodule.dense_iff_topologicalClosure_eq_top.1 hd).ge
  have hb : ⇑b = e := HilbertBasis.coe_mk he _
  refine ⟨b.repr, fun x n => ?_, fun c => ?_⟩
  · rw [b.repr_apply_apply, hb]
  · simpa [hb] using b.hasSum_repr_symm c

end M1Analyse
