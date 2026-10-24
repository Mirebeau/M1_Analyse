/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import M1Analyse.TopologieGenerale.Continuite

/-!
# §C Dualité de Legendre-Fenchel (`sec:LegendreFenchel`)

Source : `Include/LegendreFenchel.tex` (annexe), section `sec:LegendreFenchel`.

Les fonctions du cours sont à valeurs dans `ℝ̄ = EReal`, et le plus souvent dans `]-∞, ∞]`
(hypothèse `∀ x, f x ≠ ⊥`). Mathlib ne dispose ni de la conjuguée de Legendre-Fenchel, ni de la
convexité pour des fonctions à valeurs dans `EReal` (qui n'est pas un `ℝ`-module) : on introduit
donc les notions propres au cours `conjuguee`, `biconjuguee`, `domaine`, `Propre`,
`ConvexeEtendue`, `sousDiff` et `enveloppeSci`. La convexité d'une fonction à valeurs dans
`]-∞, ∞]` est définie par la convexité de son sur-graphe, et reliée à `ConvexOn` pour les
fonctions réelles.
-/

open Set Filter Topology

namespace M1Analyse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Définitions -/

/-- **Déf. `def:legendre_fenchel` (Conjuguée de Legendre-Fenchel).** Pour `f : E → ℝ̄`, on pose
`f*(φ) := sup_{x ∈ E} ⟨φ, x⟩ - f(x)` pour `φ ∈ E*`. (Soustraction de `EReal` : `a - ⊤ = ⊥`.)
Lien avec Mathlib : Mathlib n'a pas (encore) de conjuguée de Legendre-Fenchel ; `EReal` est la
droite achevée `ℝ̄` de Mathlib. -/
noncomputable def conjuguee (f : E → EReal) (φ : StrongDual ℝ E) : EReal :=
  ⨆ x, ((φ x : ℝ) : EReal) - f x

/-- La biconjuguée `f** : E → ℝ̄`, i.e. `(f*)*` restreinte à `E` via l'injection canonique
`E → E**` (« moyennant l'identification `E = E**` »). -/
noncomputable def biconjuguee (f : E → EReal) (x : E) : EReal :=
  conjuguee (conjuguee f) (NormedSpace.inclusionInDoubleDual ℝ E x)

theorem biconjuguee_apply (f : E → EReal) (x : E) :
    biconjuguee f x = ⨆ φ : StrongDual ℝ E, ((φ x : ℝ) : EReal) - conjuguee f φ :=
  rfl

/-- **Déf. `def:domaineFct` (Domaine d'une fonction).** `Dom(f) := {x ∈ X | f(x) < ∞}`. -/
def domaine {X : Type*} (f : X → EReal) : Set X :=
  {x | f x < ⊤}

/-- **Déf. `def:domaineFct` (Fonction propre).** Une fonction `f : X → ]-∞, ∞]` est propre si
`Dom(f) ≠ ∅`. (La condition `f > -∞` encode l'espace d'arrivée `]-∞, ∞]`.) -/
def Propre {X : Type*} (f : X → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (domaine f).Nonempty

/-- Convexité d'une fonction `f : E → ]-∞, ∞]` : son sur-graphe `{(x, t) ∈ E × ℝ | f(x) ≤ t}`
est convexe. Remarque : notion utilisée par le cours sans définition explicite pour les fonctions
à valeurs dans `]-∞, ∞]` ; elle coïncide avec `ConvexOn` pour les fonctions réelles
(`convexeEtendue_coe_iff`). -/
def ConvexeEtendue {F : Type*} [AddCommGroup F] [Module ℝ F] (f : F → EReal) : Prop :=
  Convex ℝ {p : F × ℝ | f p.1 ≤ p.2}

/-- Pour une fonction réelle `g`, `ConvexeEtendue` coïncide avec `ConvexOn ℝ univ g`. -/
theorem convexeEtendue_coe_iff {F : Type*} [AddCommGroup F] [Module ℝ F] (g : F → ℝ) :
    ConvexeEtendue (fun x => (g x : EReal)) ↔ ConvexOn ℝ univ g := by
  simp only [ConvexeEtendue, EReal.coe_le_coe_iff]
  constructor
  · intro h
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have := h (x := (x, g x)) (y := (y, g y)) (by simp) (by simp) ha hb hab
    simpa using this
  · intro h p hp q hq a b ha hb hab
    simp only [mem_ofPred_eq, Prod.fst_add, Prod.smul_fst, smul_eq_mul, Prod.snd_add,
      Prod.smul_snd] at hp hq ⊢
    calc g (a • p.1 + b • q.1) ≤ a • g p.1 + b • g q.1 :=
          h.2 (mem_univ _) (mem_univ _) ha hb hab
      _ ≤ a * p.2 + b * q.2 := by
          simp only [smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)

/-- Forme utilisable de la convexité : si `f x ≤ s` et `f y ≤ t` (réels), alors
`f(a x + b y) ≤ a s + b t` pour `a, b ≥ 0`, `a + b = 1`. -/
theorem ConvexeEtendue.le_comb {F : Type*} [AddCommGroup F] [Module ℝ F] {f : F → EReal}
    (hf : ConvexeEtendue f) {x y : F} {s t : ℝ} (hx : f x ≤ s) (hy : f y ≤ t) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * s + b * t : ℝ) : EReal) := by
  have := hf (x := (x, s)) (y := (y, t)) hx hy ha hb hab
  simpa using this

/-! ### Lemmes techniques sur `EReal` -/

theorem coe_sub_le_coe_iff (a b : ℝ) (y : EReal) :
    (a : EReal) - y ≤ b ↔ ((a - b : ℝ) : EReal) ≤ y := by
  induction y using EReal.rec with
  | bot =>
    simp only [EReal.coe_sub_bot, top_le_iff, le_bot_iff, EReal.coe_ne_top, EReal.coe_ne_bot]
  | top => simp [EReal.sub_top]
  | coe r =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

theorem coe_lt_coe_sub_iff (a b : ℝ) (y : EReal) :
    (b : EReal) < (a : EReal) - y ↔ y < ((a - b : ℝ) : EReal) := by
  rw [← not_le, ← not_le, coe_sub_le_coe_iff]

/-- Le supremum d'une famille de fonctions affines continues `x ↦ ⟨Lᵢ, x⟩ - cᵢ` (avec
`cᵢ ∈ ℝ̄`) est convexe et s.c.i. -/
theorem convexeEtendue_lsc_iSup {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {ι : Type*} (L : ι → StrongDual ℝ X) (c : ι → EReal) :
    ConvexeEtendue (fun x => ⨆ i, ((L i x : ℝ) : EReal) - c i) ∧
    LowerSemicontinuous (fun x => ⨆ i, ((L i x : ℝ) : EReal) - c i) := by
  constructor
  · have : {p : X × ℝ | ⨆ i, ((L i p.1 : ℝ) : EReal) - c i ≤ p.2} =
        ⋂ i, (fun p : X × ℝ => L i p.1 - p.2) ⁻¹' {s : ℝ | (s : EReal) ≤ c i} := by
      ext p
      simp [iSup_le_iff, coe_sub_le_coe_iff]
    rw [ConvexeEtendue, this]
    refine convex_iInter fun i => Convex.is_linear_preimage ?_ ?_
    · exact Set.OrdConnected.convex ⟨fun a _ b hb z hz =>
        le_trans (EReal.coe_le_coe_iff.mpr hz.2) hb⟩
    · exact ((L i).toLinearMap.comp (LinearMap.fst ℝ X ℝ) - LinearMap.snd ℝ X ℝ).isLinear
  · refine lowerSemicontinuous_iSup fun i => ?_
    induction c i using EReal.rec with
    | bot => simpa [EReal.coe_sub_bot] using lowerSemicontinuous_const
    | top => simpa [EReal.sub_top] using lowerSemicontinuous_const
    | coe r =>
      simp_rw [← EReal.coe_sub]
      exact (continuous_coe_real_ereal.comp
        ((L i).continuous.sub continuous_const)).lowerSemicontinuous

/-! ### Exemple et lemme `lem:FenchelPropre` -/

/-- **Déf. `def:legendre_fenchel`, exemple.** Si `f(x) = ½‖x‖²`, alors `f*(φ) = ½‖φ‖²`. -/
theorem def_legendre_fenchel_exemple (φ : StrongDual ℝ E) :
    conjuguee (fun x : E => ((1 / 2 * ‖x‖ ^ 2 : ℝ) : EReal)) φ =
      ((1 / 2 * ‖φ‖ ^ 2 : ℝ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h1 : φ x ≤ ‖φ‖ * ‖x‖ := (le_abs_self _).trans (φ.le_opNorm x)
    nlinarith [sq_nonneg (‖φ‖ - ‖x‖)]
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨t, hct, ht⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    rw [EReal.coe_lt_coe_iff] at ht
    refine lt_of_lt_of_le hct ?_
    set N := ‖φ‖ with hNdef
    rcases (norm_nonneg φ).eq_or_lt with h0 | hN
    · refine le_trans ?_ (le_iSup _ (0 : E))
      rw [hNdef, ← h0] at ht
      simp only [map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, mul_zero, EReal.coe_zero, sub_zero]
      norm_num at ht
      exact_mod_cast ht.le
    set r := ((t + 1 / 2 * N ^ 2) / N + N) / 2 with hr
    have hr1 : (t + 1 / 2 * N ^ 2) / N < N := by
      rw [div_lt_iff₀ hN]
      nlinarith
    have hrN : r < N := by linarith
    have hr2 : t < N * r - 1 / 2 * N ^ 2 := by
      have : t + 1 / 2 * N ^ 2 < N * r := by
        have := (div_lt_iff₀ hN).mp (show (t + 1 / 2 * N ^ 2) / N < r by linarith)
        linarith
      linarith
    obtain ⟨y, hy1, hy2⟩ := φ.exists_lt_apply_of_lt_opNorm hrN
    rw [Real.norm_eq_abs] at hy2
    obtain ⟨z, hz1, hz2⟩ : ∃ z : E, ‖z‖ < 1 ∧ r < φ z := by
      rcases le_or_gt 0 (φ y) with h | h
      · exact ⟨y, hy1, by rwa [abs_of_nonneg h] at hy2⟩
      · exact ⟨-y, by rwa [norm_neg], by rw [map_neg]; rwa [abs_of_neg h] at hy2⟩
    refine le_trans ?_ (le_iSup _ (N • z))
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff, map_smul, smul_eq_mul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hN]
    have hz0 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    nlinarith [mul_le_mul_of_nonneg_left hz0 (sq_nonneg N)]

/-- Inégalité de Fenchel-Young : `⟨φ, x⟩ - f(x) ≤ f*(φ)`. -/
theorem le_conjuguee (f : E → EReal) (φ : StrongDual ℝ E) (x : E) :
    ((φ x : ℝ) : EReal) - f x ≤ conjuguee f φ :=
  le_iSup (fun x => ((φ x : ℝ) : EReal) - f x) x

/-- **Lemme `lem:FenchelPropre` (minorants affines).** Pour tous `α ∈ ℝ`, `φ ∈ E*`, on a
`f ≥ φ + α` ssi `f*(φ) ≤ -α`. -/
theorem lem_FenchelPropre_minorant (f : E → EReal) (φ : StrongDual ℝ E) (α : ℝ) :
    (∀ x, ((φ x + α : ℝ) : EReal) ≤ f x) ↔ conjuguee f φ ≤ ((-α : ℝ) : EReal) := by
  simp only [conjuguee, iSup_le_iff, coe_sub_le_coe_iff, sub_neg_eq_add]

/-- **Lemme `lem:FenchelPropre`.** Si `f : E → ]-∞, ∞]` est propre, alors
`f* : E* → ]-∞, ∞]` est convexe et s.c.i. ; de plus `f*` est propre ssi `f` admet un minorant
affine continu. -/
theorem lem_FenchelPropre (f : E → EReal) (hf : Propre f) :
    (∀ φ, conjuguee f φ ≠ ⊥) ∧ ConvexeEtendue (conjuguee f) ∧
    LowerSemicontinuous (conjuguee f) ∧
    (Propre (conjuguee f) ↔
      ∃ (φ : StrongDual ℝ E) (α : ℝ), ∀ x, ((φ x + α : ℝ) : EReal) ≤ f x) := by
  obtain ⟨hbot, x₁, hx₁⟩ := hf
  have hne : ∀ φ, conjuguee f φ ≠ ⊥ := by
    intro φ
    refine bot_lt_iff_ne_bot.mp (lt_of_lt_of_le ?_ (le_conjuguee f φ x₁))
    obtain ⟨r, hr⟩ : ∃ r : ℝ, f x₁ = r := by
      lift f x₁ to ℝ using ⟨hx₁.ne, hbot x₁⟩ with r
      exact ⟨r, rfl⟩
    rw [hr, ← EReal.coe_sub]
    exact EReal.bot_lt_coe _
  have hcl := convexeEtendue_lsc_iSup (fun x : E => NormedSpace.inclusionInDoubleDual ℝ E x) f
  refine ⟨hne, hcl.1, hcl.2, ?_⟩
  constructor
  · rintro ⟨-, φ, hφ⟩
    lift conjuguee f φ to ℝ using ⟨hφ.ne, hne φ⟩ with s hs
    exact ⟨φ, -s, (lem_FenchelPropre_minorant f φ (-s)).mpr (by rw [← hs, neg_neg])⟩
  · rintro ⟨φ, α, h⟩
    exact ⟨hne, φ, lt_of_le_of_lt ((lem_FenchelPropre_minorant f φ α).mp h)
      (EReal.coe_lt_top _)⟩

/-! ### Lemme `lem:minorantCvxSci` -/

/-- Toute valeur `f x ≠ ±∞` est réelle. -/
theorem exists_coe_eq {X : Type*} {f : X → EReal} (hbot : ∀ x, f x ≠ ⊥) {x : X}
    (htop : f x ≠ ⊤) : ∃ s : ℝ, f x = s :=
  ⟨(f x).toReal, (EReal.coe_toReal htop (hbot x)).symm⟩

/-- Séparation (Hahn-Banach) du point `(x₀, t₀)` et du sur-graphe fermé convexe de `f`, la forme
linéaire continue sur `E × ℝ` étant écrite `(x, t) ↦ ψ(x) + t l`. -/
theorem sep_surGraphe {f : E → EReal} (hc : ConvexeEtendue f) (hl : LowerSemicontinuous f)
    {x₀ : E} {t₀ : ℝ} (ht : (t₀ : EReal) < f x₀) :
    ∃ (ψ : StrongDual ℝ E) (l u : ℝ), ψ x₀ + t₀ * l < u ∧
      ∀ x (s : ℝ), f x ≤ s → u < ψ x + s * l := by
  obtain ⟨L, u, h1, h2⟩ := geometric_hahn_banach_point_closed hc
    ((lowerSemicontinuous_iff_isClosed_surGraphe f).mp hl) (x := (x₀, t₀))
    (fun h => absurd h (not_le.mpr ht))
  have hL : ∀ (x : E) (t : ℝ),
      L (x, t) = (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) x + t * L (0, 1) := by
    intro x t
    have : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  refine ⟨L.comp (ContinuousLinearMap.inl ℝ E ℝ), L (0, 1), u, by rw [← hL]; exact h1,
    fun x s hs => by rw [← hL]; exact h2 (x, s) hs⟩

/-- Construction du minorant affine dans le cas `l > 0`. -/
theorem minorant_of_sep {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥) {x₀ : E} {t₀ : ℝ}
    (ψ : StrongDual ℝ E) {l u : ℝ} (hl : 0 < l) (h0 : ψ x₀ + t₀ * l < u)
    (hC : ∀ x (s : ℝ), f x ≤ s → u < ψ x + s * l) :
    ∃ (α : ℝ) (φ : StrongDual ℝ E), (∀ x, ((α + φ x : ℝ) : EReal) < f x) ∧ t₀ < α + φ x₀ := by
  have key : ∀ x, u / l + (-l⁻¹ • ψ) x = (u - ψ x) / l := by
    intro x
    simp only [smul_apply, smul_eq_mul]
    ring
  refine ⟨u / l, -l⁻¹ • ψ, fun x => ?_, ?_⟩
  · by_cases htop : f x = ⊤
    · rw [htop]
      exact EReal.coe_lt_top _
    obtain ⟨s, hs⟩ := exists_coe_eq hbot htop
    rw [hs, EReal.coe_lt_coe_iff, key, div_lt_iff₀ hl]
    linarith [hC x s hs.le]
  · rw [key, lt_div_iff₀ hl]
    linarith

/-- Cas `f(x₀) < ∞` du lemme `lem:minorantCvxSci`. -/
theorem minorant_of_ne_top {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥) (hc : ConvexeEtendue f)
    (hl : LowerSemicontinuous f) {x₀ : E} {t₀ : ℝ} (ht : (t₀ : EReal) < f x₀)
    (hfin : f x₀ ≠ ⊤) :
    ∃ (α : ℝ) (φ : StrongDual ℝ E), (∀ x, ((α + φ x : ℝ) : EReal) < f x) ∧ t₀ < α + φ x₀ := by
  obtain ⟨ψ, l, u, h0, hC⟩ := sep_surGraphe hc hl ht
  obtain ⟨s₀, hs₀⟩ := exists_coe_eq hbot hfin
  rw [hs₀, EReal.coe_lt_coe_iff] at ht
  have h1 := hC x₀ s₀ hs₀.le
  have hlpos : 0 < l := by
    by_contra hneg
    push Not at hneg
    nlinarith
  exact minorant_of_sep hbot ψ hlpos h0 hC

/-- **Lemme `lem:minorantCvxSci`.** Soit `f : E → ]-∞, ∞]` convexe et s.c.i., et soient
`x₀ ∈ E` et `t₀ < f(x₀)`. Alors il existe `α ∈ ℝ`, `φ ∈ E*` tels que `f > α + φ` sur `E`, et
`α + φ(x₀) > t₀`. -/
theorem lem_minorantCvxSci (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hc : ConvexeEtendue f)
    (hl : LowerSemicontinuous f) (x₀ : E) (t₀ : ℝ) (ht : (t₀ : EReal) < f x₀) :
    ∃ (α : ℝ) (φ : StrongDual ℝ E), (∀ x, ((α + φ x : ℝ) : EReal) < f x) ∧ t₀ < α + φ x₀ := by
  by_cases hfin : f x₀ ≠ ⊤
  · exact minorant_of_ne_top hbot hc hl ht hfin
  push Not at hfin
  obtain ⟨ψ, l, u, h0, hC⟩ := sep_surGraphe hc hl ht
  by_cases hlpos : 0 < l
  · exact minorant_of_sep hbot ψ hlpos h0 hC
  push Not at hlpos
  by_cases hdom : ∃ x₁, f x₁ ≠ ⊤
  swap
  · push Not at hdom
    refine ⟨t₀ + 1, 0, fun x => ?_, by simp⟩
    rw [hdom x]
    exact EReal.coe_lt_top _
  obtain ⟨x₁, hx₁⟩ := hdom
  obtain ⟨s₁, hs₁⟩ := exists_coe_eq hbot hx₁
  obtain ⟨α₁, φ₁, hmin₁, -⟩ := minorant_of_ne_top hbot hc hl (t₀ := s₁ - 1)
    (by rw [hs₁, EReal.coe_lt_coe_iff]; linarith) hx₁
  -- `l = 0`
  have hl0 : l = 0 := by
    refine le_antisymm hlpos (not_lt.mp fun hneg => ?_)
    set s := max s₁ ((u - ψ x₁) / l)
    have h1 := hC x₁ s (by rw [hs₁, EReal.coe_le_coe_iff]; exact le_max_left _ _)
    have h2 : s * l ≤ u - ψ x₁ := (div_le_iff_of_neg hneg).mp (le_max_right _ _)
    linarith
  subst hl0
  simp only [mul_zero, add_zero] at h0 hC
  have hpos : 0 < u - ψ x₀ := by linarith
  set μ := (|t₀ - α₁ - φ₁ x₀| + 1) / (u - ψ x₀) with hμ
  have hμpos : 0 < μ := div_pos (by positivity) hpos
  refine ⟨α₁ + μ * u, φ₁ - μ • ψ, fun x => ?_, ?_⟩
  · by_cases htop : f x = ⊤
    · rw [htop]
      exact EReal.coe_lt_top _
    obtain ⟨s, hs⟩ := exists_coe_eq hbot htop
    have h1 := hC x s hs.le
    have h2 := hmin₁ x
    rw [hs, EReal.coe_lt_coe_iff] at h2 ⊢
    simp only [sub_apply, smul_apply, smul_eq_mul]
    nlinarith [mul_pos hμpos (sub_pos.mpr h1)]
  · simp only [sub_apply, smul_apply, smul_eq_mul]
    have : μ * (u - ψ x₀) = |t₀ - α₁ - φ₁ x₀| + 1 := div_mul_cancel₀ _ hpos.ne'
    nlinarith [le_abs_self (t₀ - α₁ - φ₁ x₀)]

/-! ### Théorème `th:LegendreFenchel` -/

/-- Si `f ≤ g` alors `f* ≥ g*`. -/
theorem conjuguee_anti {f g : E → EReal} (h : ∀ x, f x ≤ g x) (φ : StrongDual ℝ E) :
    conjuguee g φ ≤ conjuguee f φ :=
  iSup_mono fun x => EReal.sub_le_sub le_rfl (h x)

/-- `f** ≤ f`. -/
theorem biconjuguee_le (f : E → EReal) (x : E) : biconjuguee f x ≤ f x := by
  refine iSup_le fun φ => ?_
  by_cases htop : f x = ⊤
  · rw [htop]
    exact le_top
  by_cases hbot : f x = ⊥
  · have := le_conjuguee f φ x
    rw [hbot, EReal.coe_sub_bot, top_le_iff] at this
    change ((φ x : ℝ) : EReal) - conjuguee f φ ≤ f x
    rw [this, EReal.sub_top]
    exact bot_le
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  change ((φ x : ℝ) : EReal) - conjuguee f φ ≤ f x
  rw [hr, coe_sub_le_coe_iff]
  have := le_conjuguee f φ x
  rwa [hr, ← EReal.coe_sub] at this

/-- **Thm. `th:LegendreFenchel` (Dualité de Legendre-Fenchel).** Soit `f : E → ]-∞, ∞]` propre
et admettant un minorant affine (continu) sur un evn. Alors `f**` est convexe, s.c.i., propre,
et `f** ≤ f` sur `E`, avec égalité ssi `f` est convexe et s.c.i. -/
theorem th_LegendreFenchel (f : E → EReal) (hf : Propre f)
    (hmin : ∃ (φ : StrongDual ℝ E) (α : ℝ), ∀ x, ((φ x + α : ℝ) : EReal) ≤ f x) :
    ConvexeEtendue (biconjuguee f) ∧ LowerSemicontinuous (biconjuguee f) ∧
    Propre (biconjuguee f) ∧ (∀ x, biconjuguee f x ≤ f x) ∧
    (biconjuguee f = f ↔ ConvexeEtendue f ∧ LowerSemicontinuous f) := by
  have hcl := convexeEtendue_lsc_iSup (fun φ : StrongDual ℝ E => φ) (conjuguee f)
  obtain ⟨hbot, x₁, hx₁⟩ := hf
  refine ⟨hcl.1, hcl.2, ⟨fun x => ?_, x₁, lt_of_le_of_lt (biconjuguee_le f x₁) hx₁⟩,
    biconjuguee_le f, ⟨fun h => h ▸ hcl, fun ⟨hc, hl⟩ => ?_⟩⟩
  · obtain ⟨φ₀, α₀, h⟩ := hmin
    have hφ₀ := (lem_FenchelPropre_minorant f φ₀ α₀).mp h
    refine bot_lt_iff_ne_bot.mp (lt_trans (EReal.bot_lt_coe (φ₀ x + α₀ - 1))
      (lt_of_lt_of_le ?_ (le_iSup (fun φ : StrongDual ℝ E =>
        ((φ x : ℝ) : EReal) - conjuguee f φ) φ₀)))
    rw [coe_lt_coe_sub_iff]
    exact lt_of_le_of_lt hφ₀ (EReal.coe_lt_coe_iff.mpr (by linarith))
  · funext x₀
    refine le_antisymm (biconjuguee_le f x₀) (not_lt.mp fun hlt => ?_)
    obtain ⟨t₀, ht₁, ht₂⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    obtain ⟨α, φ, hφ, hx₀⟩ := lem_minorantCvxSci f hbot hc hl x₀ t₀ ht₂
    have hφ' := (lem_FenchelPropre_minorant f φ α).mp fun x => by
      rw [add_comm]
      exact (hφ x).le
    have : (t₀ : EReal) < ((φ x₀ : ℝ) : EReal) - conjuguee f φ := by
      rw [coe_lt_coe_sub_iff]
      exact lt_of_le_of_lt hφ' (EReal.coe_lt_coe_iff.mpr (by linarith))
    exact absurd (lt_of_lt_of_le this (le_iSup (fun φ : StrongDual ℝ E =>
      ((φ x₀ : ℝ) : EReal) - conjuguee f φ) φ)) (not_lt.mpr ht₁.le)

/-- **Thm. `th:LegendreFenchel`, suite (Minorant affine).** Une fonction `f : E → ]-∞, ∞]`
propre, convexe et s.c.i. admet un minorant affine continu. -/
theorem th_LegendreFenchel_minorant (f : E → EReal) (hf : Propre f) (hc : ConvexeEtendue f)
    (hl : LowerSemicontinuous f) :
    ∃ (φ : StrongDual ℝ E) (α : ℝ), ∀ x, ((φ x + α : ℝ) : EReal) ≤ f x := by
  obtain ⟨hbot, x₁, hx₁⟩ := hf
  obtain ⟨s₁, hs₁⟩ := exists_coe_eq hbot hx₁.ne
  obtain ⟨α, φ, hφ, -⟩ := lem_minorantCvxSci f hbot hc hl x₁ (s₁ - 1)
    (by rw [hs₁, EReal.coe_lt_coe_iff]; linarith)
  exact ⟨φ, α, fun x => by rw [add_comm]; exact (hφ x).le⟩

/-- **Thm. `th:LegendreFenchel`, suite (Enveloppe convexe s.c.i.).** Si `f` est propre, `f**`
est la plus grande fonction convexe s.c.i. `h : E → ]-∞, ∞]` bornée supérieurement par `f`. -/
theorem th_LegendreFenchel_plusGrande (f : E → EReal) (hf : Propre f) (h : E → EReal)
    (hbot : ∀ x, h x ≠ ⊥) (hc : ConvexeEtendue h) (hl : LowerSemicontinuous h)
    (hle : ∀ x, h x ≤ f x) (x : E) : h x ≤ biconjuguee f x := by
  obtain ⟨-, x₁, hx₁⟩ := hf
  have hh : Propre h := ⟨hbot, x₁, lt_of_le_of_lt (hle x₁) hx₁⟩
  have heq := ((th_LegendreFenchel h hh (th_LegendreFenchel_minorant h hh hc hl)).2.2.2.2).mpr
    ⟨hc, hl⟩
  rw [← heq]
  exact iSup_mono fun φ => EReal.sub_le_sub le_rfl (conjuguee_anti hle φ)

/-! ### Lemmes `lem:cvxImplLip` et `lem:cvxImplBorne` -/

/-- Première partie de `lem:cvxImplLip`, avec `f(x) = a` réel. -/
theorem lip_aux {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥) (hc : ConvexeEtendue f) {x : E}
    {a r M : ℝ} (hr : 0 < r) (hx : f x = a)
    (hB : ∀ y ∈ Metric.closedBall x r, f y ≤ ((a + M : ℝ) : EReal)) :
    ∀ y ∈ Metric.closedBall x r, ∃ b : ℝ, f y = b ∧ |a - b| ≤ M / r * ‖x - y‖ := by
  -- majoration `f(y) ≤ a + (M / r) ‖y - x‖`
  have hU : ∀ y ∈ Metric.closedBall x r, f y ≤ ((a + M / r * ‖y - x‖ : ℝ) : EReal) := by
    intro y hy
    have hdr : ‖y - x‖ ≤ r := by rwa [Metric.mem_closedBall, dist_eq_norm] at hy
    rcases (norm_nonneg (y - x)).eq_or_lt with h0 | hdpos
    · have : y = x := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
      rw [← h0, this, hx]
      simp
    set w := x + (r / ‖y - x‖) • (y - x) with hwdef
    have hw : w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall, dist_eq_norm, hwdef, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos hr hdpos), div_mul_cancel₀ _ hdpos.ne']
    have hyw : y = (1 - ‖y - x‖ / r) • x + (‖y - x‖ / r) • w := by
      have hk : ‖y - x‖ / r * (r / ‖y - x‖) = 1 := by field_simp
      have : (1 - ‖y - x‖ / r) • x + (‖y - x‖ / r) • w =
          x + (‖y - x‖ / r * (r / ‖y - x‖)) • (y - x) := by
        rw [hwdef]
        module
      rw [this, hk, one_smul, add_sub_cancel]
    have := hc.le_comb (x := x) (y := w) (s := a) (t := a + M) hx.le (hB w hw)
      (sub_nonneg.mpr ((div_le_one hr).mpr hdr)) (div_nonneg hdpos.le hr.le) (by ring)
    rw [← hyw] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    ring
  intro y hy
  have hy' : x - (y - x) ∈ Metric.closedBall x r := by
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, ← dist_eq_norm]
  obtain ⟨b, hb⟩ := exists_coe_eq hbot (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hU y hy))
  obtain ⟨b', hb'⟩ :=
    exists_coe_eq hbot (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hU _ hy'))
  have h1 := hU y hy
  rw [hb, EReal.coe_le_coe_iff] at h1
  have h2 := hU _ hy'
  rw [hb', EReal.coe_le_coe_iff, sub_sub_cancel_left, norm_neg] at h2
  have h3 := hc.le_comb (x := y) (y := x - (y - x)) hb.le hb'.le
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (x - (y - x)) = x := by module
  rw [e, hx, EReal.coe_le_coe_iff] at h3
  refine ⟨b, hb, ?_⟩
  rw [norm_sub_rev, abs_le]
  constructor <;> linarith

/-- **Lemme `lem:cvxImplLip` (Convexe implique localement Lipschitz).** Soit `f : E → ]-∞, ∞]`
convexe sur un evn. Supposons `f ≤ f(x) + M` sur `B'(x, r)`, où `x ∈ E`, `r > 0`, `M > 0`.
Alors `|f(x) - f(y)| ≤ (M / r) ‖x - y‖` pour tout `y ∈ B'(x, r)`, et `f` est `2M/r`-Lipschitz
sur `B'(x, r/3)`.
Remarque : on suppose de plus `f(x) < ∞`, implicite dans le cours (sinon l'hypothèse
`f ≤ f(x) + M` est vide) ; `f` est alors finie sur `B'(x, r)`, et les valeurs absolues portent
sur les valeurs réelles `(f y).toReal`. -/
theorem lem_cvxImplLip (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hc : ConvexeEtendue f) (x : E)
    (r M : ℝ) (hr : 0 < r) (hM : 0 < M) (hx : f x ≠ ⊤)
    (hB : ∀ y ∈ Metric.closedBall x r, f y ≤ f x + M) :
    (∀ y ∈ Metric.closedBall x r,
      f y ≠ ⊤ ∧ |(f x).toReal - (f y).toReal| ≤ M / r * ‖x - y‖) ∧
    (∀ y ∈ Metric.closedBall x (r / 3), ∀ z ∈ Metric.closedBall x (r / 3),
      |(f y).toReal - (f z).toReal| ≤ 2 * M / r * ‖y - z‖) := by
  obtain ⟨a, ha⟩ := exists_coe_eq hbot hx
  have hB' : ∀ y ∈ Metric.closedBall x r, f y ≤ ((a + M : ℝ) : EReal) := by
    intro y hy
    rw [EReal.coe_add, ← ha]
    exact hB y hy
  have P1 := lip_aux hbot hc hr ha hB'
  refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
  · obtain ⟨b, hb, hab⟩ := P1 y hy
    rw [ha, hb]
    exact ⟨EReal.coe_ne_top b, by simpa using hab⟩
  have hyr : y ∈ Metric.closedBall x r :=
    Metric.closedBall_subset_closedBall (by linarith) hy
  obtain ⟨b, hb, hab⟩ := P1 y hyr
  have hdy : ‖x - y‖ ≤ r / 3 := by
    rw [norm_sub_rev, ← dist_eq_norm]
    exact hy
  have hb3 : a ≤ b + M / 3 := by
    have h1 : M / r * ‖x - y‖ ≤ M / r * (r / 3) :=
      mul_le_mul_of_nonneg_left hdy (div_pos hM hr).le
    have h2 : M / r * (r / 3) = M / 3 := by field_simp
    linarith [le_abs_self (a - b)]
  have hB2 : ∀ w ∈ Metric.closedBall y (2 * r / 3), f w ≤ ((b + 4 * M / 3 : ℝ) : EReal) := by
    intro w hw
    have hwx : w ∈ Metric.closedBall x r := by
      rw [Metric.mem_closedBall] at hw hy ⊢
      linarith [dist_triangle w y x]
    exact (hB' w hwx).trans (EReal.coe_le_coe_iff.mpr (by linarith))
  have hzy : z ∈ Metric.closedBall y (2 * r / 3) := by
    rw [Metric.mem_closedBall] at hz hy ⊢
    linarith [dist_triangle z x y, dist_comm x y]
  obtain ⟨c, hzc, hbc⟩ := lip_aux hbot hc (by positivity) hb hB2 z hzy
  have e : 4 * M / 3 / (2 * r / 3) = 2 * M / r := by field_simp; ring
  rw [e] at hbc
  rw [hb, hzc]
  simpa using hbc

/-- Majoration locale (argument de Baire) : une fonction convexe s.c.i. sur un Banach est
majorée au voisinage de tout point de l'intérieur de son domaine. -/
theorem majoration_locale [CompleteSpace E] {f : E → EReal} (hbot : ∀ x, f x ≠ ⊥)
    (hc : ConvexeEtendue f) (hl : LowerSemicontinuous f) {x₀ : E}
    (hx₀ : x₀ ∈ interior (domaine f)) :
    ∃ ρ > 0, ∃ N : ℝ, ∀ w ∈ Metric.ball x₀ ρ, f w ≤ N := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
  obtain ⟨a₀, ha₀⟩ := exists_coe_eq hbot (hball (Metric.mem_ball_self hε)).ne
  set C : ℕ → Set E := fun n =>
    {v | f (x₀ + ((n : ℝ) + 1)⁻¹ • v) ≤ (((n : ℝ) + 1 : ℝ) : EReal) ∧
      f (x₀ + ((n : ℝ) + 1)⁻¹ • -v) ≤ (((n : ℝ) + 1 : ℝ) : EReal)} with hC
  have hcl : ∀ n, IsClosed (C n) := fun n =>
    ((hl.isClosed_preimage _).preimage (continuous_const.add
      (continuous_const.smul continuous_id))).inter
    ((hl.isClosed_preimage _).preimage (continuous_const.add
      (continuous_const.smul continuous_neg)))
  have hcover : ⋃ n, C n = univ := by
    refine eq_univ_of_forall fun v => mem_iUnion.mpr ?_
    obtain ⟨k, hk⟩ := exists_nat_gt (‖v‖ / ε)
    set K : ℝ := (k : ℝ) + 1 with hK
    have hKpos : 0 < K := by positivity
    have hvK : ‖v‖ < ε * K := by
      rw [div_lt_iff₀ hε] at hk
      linarith
    have hdom : ∀ u : E, ‖u‖ = ‖v‖ → ∃ c : ℝ, f (x₀ + K⁻¹ • u) = c := by
      intro u hu
      refine exists_coe_eq hbot (hball ?_).ne
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_inv,
        Real.norm_eq_abs, abs_of_pos hKpos, hu, inv_mul_lt_iff₀ hKpos]
      linarith
    obtain ⟨c₁, hc₁⟩ := hdom v rfl
    obtain ⟨c₂, hc₂⟩ := hdom (-v) (norm_neg v)
    set B := max (max |a₀| |c₁|) |c₂|
    obtain ⟨m, hm⟩ := exists_nat_gt B
    refine ⟨max k m, ?_⟩
    set N : ℝ := ((max k m : ℕ) : ℝ) + 1 with hN
    have hKN : K ≤ N := by
      simp only [hK, hN, add_le_add_iff_right, Nat.cast_le]
      exact le_max_left _ _
    have hBN : B ≤ N := by
      have : (m : ℝ) ≤ ((max k m : ℕ) : ℝ) := Nat.cast_le.mpr (le_max_right _ _)
      linarith
    have hNpos : 0 < N := by positivity
    have key : ∀ u : E, ∀ c : ℝ, f (x₀ + K⁻¹ • u) = c → |c| ≤ B →
        f (x₀ + N⁻¹ • u) ≤ (N : EReal) := by
      intro u c hu hcB
      have e : x₀ + N⁻¹ • u = (1 - K / N) • x₀ + (K / N) • (x₀ + K⁻¹ • u) := by
        have : K / N * K⁻¹ = N⁻¹ := by field_simp
        rw [← this]
        module
      have h0 : f x₀ ≤ (B : EReal) := by
        rw [ha₀, EReal.coe_le_coe_iff]
        exact (le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _))
      have h1 : f (x₀ + K⁻¹ • u) ≤ (B : EReal) := by
        rw [hu, EReal.coe_le_coe_iff]
        exact (le_abs_self _).trans hcB
      have := hc.le_comb h0 h1 (sub_nonneg.mpr ((div_le_one hNpos).mpr hKN))
        (div_nonneg hKpos.le hNpos.le) (by ring)
      rw [← e] at this
      refine this.trans (EReal.coe_le_coe_iff.mpr ?_)
      have : (1 - K / N) * B + K / N * B = B := by ring
      linarith
    exact ⟨key v c₁ hc₁ ((le_max_right _ _).trans (le_max_left _ _)),
      key (-v) c₂ hc₂ (le_max_right _ _)⟩
  obtain ⟨n, z, hz⟩ := nonempty_interior_of_iUnion_of_closed hcl hcover
  obtain ⟨ρ, hρ, hzball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  set N : ℝ := (n : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  refine ⟨ρ / (2 * N), by positivity, N, fun w hw => ?_⟩
  set v := z + (2 * N) • (w - x₀) with hv
  have hvC : v ∈ C n := by
    refine interior_subset (hzball ?_)
    rw [Metric.mem_ball, dist_eq_norm, hv, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity), ← lt_div_iff₀' (by positivity), ← dist_eq_norm]
    exact hw
  have hzC : z ∈ C n := interior_subset hz
  have e : w = (1 / 2 : ℝ) • (x₀ + N⁻¹ • v) + (1 / 2 : ℝ) • (x₀ + N⁻¹ • -z) := by
    have : 1 / 2 * N⁻¹ * (2 * N) = 1 := by field_simp
    calc w = x₀ + (1 / 2 * N⁻¹ * (2 * N)) • (w - x₀) := by rw [this, one_smul, add_sub_cancel]
      _ = _ := by rw [hv]; module
  have := hc.le_comb hvC.1 hzC.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [← e] at this
  refine this.trans (le_of_eq ?_)
  congr 1
  ring

/-- **Lemme `lem:cvxImplBorne` (Convexe implique localement borné).** Soit `f : E → ]-∞, ∞]`
convexe s.c.i. sur un Banach. Alors `f` est localement bornée sur l'intérieur de `Dom(f)`.
Preuve (différente du cours) : Baire dans `E` tout entier, recouvert par les fermés
`{v | f(x₀ ± v/(n+1)) ≤ n+1}`, puis symétrie et convexité (`majoration_locale`) ; la
minoration au voisinage de `x₀`, non traitée dans le cours, vient de la s.c.i. -/
theorem lem_cvxImplBorne [CompleteSpace E] (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hc : ConvexeEtendue f) (hl : LowerSemicontinuous f) (x₀ : E)
    (hx₀ : x₀ ∈ interior (domaine f)) :
    ∃ U ∈ 𝓝 x₀, ∃ M : ℝ, ∀ y ∈ U, f y ≤ M ∧ ((-M : ℝ) : EReal) ≤ f y := by
  obtain ⟨ρ, hρ, N, hN⟩ := majoration_locale hbot hc hl hx₀
  have hdom : f x₀ < ⊤ := (interior_subset (s := domaine f) hx₀ :)
  obtain ⟨a₀, ha₀⟩ := exists_coe_eq hbot hdom.ne
  have hlt : ((a₀ - 1 : ℝ) : EReal) < f x₀ := by rw [ha₀, EReal.coe_lt_coe_iff]; linarith
  have hlow : ∀ᶠ y in 𝓝 x₀, ((a₀ - 1 : ℝ) : EReal) < f y := hl x₀ _ hlt
  refine ⟨Metric.ball x₀ ρ ∩ {y | ((a₀ - 1 : ℝ) : EReal) < f y},
    inter_mem (Metric.ball_mem_nhds x₀ hρ) hlow, max N (1 - a₀), fun y hy => ⟨?_, ?_⟩⟩
  · exact (hN y hy.1).trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _))
  · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) hy.2.le
    linarith [le_max_right N (1 - a₀)]

/-! ### Théorème `th:ssGrad` -/

/-- Sous-différentiel `∂f(x) := {φ ∈ E* | ∀ y ∈ E, f(y) ≥ f(x) + φ(y - x)}`. -/
def sousDiff (f : E → EReal) (x : E) : Set (StrongDual ℝ E) :=
  {φ | ∀ y, f x + ((φ (y - x) : ℝ) : EReal) ≤ f y}

/-- Une forme linéaire continue sur `E × ℝ` s'écrit `(x, t) ↦ ψ(x) + t l`. -/
theorem clm_prod_apply (L : StrongDual ℝ (E × ℝ)) (x : E) (t : ℝ) :
    L (x, t) = (L.comp (ContinuousLinearMap.inl ℝ E ℝ)) x + t * L (0, 1) := by
  have : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
  rw [this, map_add, map_smul, smul_eq_mul]
  rfl

/-- Une forme linéaire continue admettant un maximum local est nulle. -/
theorem clm_eq_zero_of_local_max {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (ψ : StrongDual ℝ X) {x₀ : X} {ρ : ℝ} (hρ : 0 < ρ)
    (hloc : ∀ y ∈ Metric.ball x₀ ρ, ψ y ≤ ψ x₀) : ψ = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [zero_apply]
  set s := ρ / (2 * (‖v‖ + 1)) with hs
  have hspos : 0 < s := by positivity
  have hsv : s * ‖v‖ < ρ := by
    rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have h1 := hloc (x₀ + s • v) (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hspos]
    exact hsv)
  have h2 := hloc (x₀ + s • -v) (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hspos, norm_neg]
    exact hsv)
  simp only [map_add, map_smul, map_neg, smul_eq_mul] at h1 h2
  have : s * ψ v = 0 := le_antisymm (by linarith) (by linarith)
  rcases mul_eq_zero.mp this with h5 | h5
  · exact absurd h5 hspos.ne'
  · exact h5

/-- **Thm. `th:ssGrad` (Sous-différentiel et sous-gradient d'une fonction convexe).** Soient `E`
un Banach et `f : E → ]-∞, ∞]` convexe et s.c.i. Alors `f` est localement Lipschitz sur
l'intérieur de `Dom(f)`, et `∂f(x)` est non vide pour tout `x` intérieur à `Dom(f)`.
Preuve (différente du cours) : pour `∂f(x₀) ≠ ∅`, Hahn-Banach géométrique (point hors de
l'intérieur d'un convexe d'intérieur non vide) appliqué à `(x₀, f(x₀))` et au sur-graphe,
via la seule majoration locale (`majoration_locale`) et non le caractère lipschitzien. -/
theorem th_ssGrad [CompleteSpace E] (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hc : ConvexeEtendue f) (hl : LowerSemicontinuous f) :
    (∀ x ∈ interior (domaine f), ∃ U ∈ 𝓝 x, ∃ K : ℝ, ∀ y ∈ U,
      f y ≠ ⊤ ∧ ∀ z ∈ U, |(f y).toReal - (f z).toReal| ≤ K * ‖y - z‖) ∧
    (∀ x ∈ interior (domaine f), (sousDiff f x).Nonempty) := by
  constructor
  · intro x hx
    obtain ⟨ρ, hρ, N, hN⟩ := majoration_locale hbot hc hl hx
    have hdom : f x < ⊤ := (interior_subset (s := domaine f) hx :)
    obtain ⟨a, ha⟩ := exists_coe_eq hbot hdom.ne
    have haN : a ≤ N := by
      have := hN x (Metric.mem_ball_self hρ)
      rwa [ha, EReal.coe_le_coe_iff] at this
    have hB : ∀ y ∈ Metric.closedBall x (ρ / 2), f y ≤ f x + ((N - a + 1 : ℝ) : EReal) := by
      intro y hy
      have hy' : y ∈ Metric.ball x ρ :=
        Metric.closedBall_subset_ball (by linarith) hy
      rw [ha, ← EReal.coe_add]
      exact (hN y hy').trans (EReal.coe_le_coe_iff.mpr (by linarith))
    have P := lem_cvxImplLip f hbot hc x (ρ / 2) (N - a + 1) (by positivity) (by linarith)
      hdom.ne hB
    refine ⟨Metric.closedBall x (ρ / 2 / 3), Metric.closedBall_mem_nhds x (by positivity),
      2 * (N - a + 1) / (ρ / 2), fun y hy => ⟨?_, fun z hz => P.2 y hy z hz⟩⟩
    exact (P.1 y (Metric.closedBall_subset_closedBall (by linarith) hy)).1
  · intro x₀ hx₀
    obtain ⟨ρ, hρ, N, hN⟩ := majoration_locale hbot hc hl hx₀
    have hdom : f x₀ < ⊤ := (interior_subset (s := domaine f) hx₀ :)
    obtain ⟨a₀, ha₀⟩ := exists_coe_eq hbot hdom.ne
    have hint : (interior {p : E × ℝ | f p.1 ≤ p.2}).Nonempty := by
      refine ⟨(x₀, N + 1), mem_interior_iff_mem_nhds.mpr (mem_of_superset
        (prod_mem_nhds (Metric.ball_mem_nhds x₀ hρ) (Ioi_mem_nhds (lt_add_one N)))
        fun p hp => (hN p.1 hp.1).trans (EReal.coe_le_coe_iff.mpr (le_of_lt hp.2)))⟩
    have hnot : (x₀, a₀) ∉ interior {p : E × ℝ | f p.1 ≤ p.2} := by
      intro h
      obtain ⟨ε, hε, hεC⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
      have hmem : (x₀, a₀ - ε / 2) ∈ Metric.ball (x₀, a₀) ε := by
        rw [Metric.mem_ball, Prod.dist_eq, dist_self, Real.dist_eq]
        simp only [sub_sub_cancel_left, abs_neg]
        rw [abs_of_pos (by positivity)]
        simp only [sup_lt_iff]
        exact ⟨hε, by linarith⟩
      have := hεC hmem
      simp only [mem_ofPred_eq] at this
      rw [ha₀, EReal.coe_le_coe_iff] at this
      linarith
    obtain ⟨L, hL0, hLmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hc hnot hint
    set ψ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hψ
    set l := L (0, 1) with hldef
    have h : ∀ x (t : ℝ), f x ≤ t → ψ x + t * l ≤ ψ x₀ + a₀ * l := by
      intro x t hxt
      rw [← clm_prod_apply, ← clm_prod_apply]
      exact hLmax (x, t) hxt
    have hl0 : l ≤ 0 := by
      have := h x₀ (a₀ + 1) (by rw [ha₀, EReal.coe_le_coe_iff]; linarith)
      linarith
    have hlneg : l < 0 := by
      refine lt_of_le_of_ne hl0 fun hzero => hL0 ?_
      have hloc : ∀ y ∈ Metric.ball x₀ ρ, ψ y ≤ ψ x₀ := by
        intro y hy
        have := h y N (hN y hy)
        rw [hzero] at this
        simpa using this
      have hψ0 : ∀ v, ψ v = 0 := fun v => by
        rw [clm_eq_zero_of_local_max ψ hρ hloc, zero_apply]
      refine ContinuousLinearMap.ext fun p => ?_
      rw [show p = (p.1, p.2) from rfl, clm_prod_apply, ← hψ, hψ0, ← hldef, hzero]
      simp
    refine ⟨(-l⁻¹) • ψ, fun y => ?_⟩
    by_cases htop : f y = ⊤
    · rw [htop]
      exact le_top
    obtain ⟨t, ht⟩ := exists_coe_eq hbot htop
    have hy := h y t ht.le
    rw [ha₀, ht, ← EReal.coe_add, EReal.coe_le_coe_iff]
    simp only [smul_apply, smul_eq_mul, map_sub]
    have e : -l⁻¹ * (ψ y - ψ x₀) = (ψ y - ψ x₀) / (-l) := by
      rw [div_neg, div_eq_inv_mul, neg_mul]
    have key : (ψ y - ψ x₀) / (-l) ≤ t - a₀ := by
      rw [div_le_iff₀ (neg_pos.mpr hlneg)]
      linarith
    rw [← mul_sub, e]
    linarith

/-! ### Lemme `lem:cvxSciAlt` -/

/-- Enveloppe s.c.i. `g(x) := liminf_{y → x} f(y)` (notée parfois `f_*`). -/
noncomputable def enveloppeSci {X : Type*} [TopologicalSpace X] (f : X → EReal) (x : X) :
    EReal :=
  liminf f (𝓝 x)

section EnveloppeSci

variable {X : Type*} [TopologicalSpace X]

theorem enveloppeSci_le (f : X → EReal) (x : X) : enveloppeSci f x ≤ f x := by
  refine liminf_le_of_frequently_le' fun h => ?_
  exact h.self_of_nhds le_rfl

theorem le_enveloppeSci {f : X → EReal} {x : X} {t : EReal} (h : ∀ᶠ y in 𝓝 x, t ≤ f y) :
    t ≤ enveloppeSci f x :=
  le_liminf_of_le (by isBoundedDefault) h

theorem frequently_lt_of_enveloppeSci_lt {f : X → EReal} {x : X} {t : EReal}
    (h : enveloppeSci f x < t) : ∃ᶠ y in 𝓝 x, f y < t :=
  frequently_lt_of_liminf_lt (by isBoundedDefault) h

theorem lowerSemicontinuous_enveloppeSci (f : X → EReal) :
    LowerSemicontinuous (enveloppeSci f) := by
  intro x t ht
  obtain ⟨t', htt', ht'⟩ := exists_between ht
  have h1 : ∀ᶠ y in 𝓝 x, t' < f y := eventually_lt_of_lt_liminf ht'
  filter_upwards [eventually_eventually_nhds.mpr h1] with z hz
  exact lt_of_lt_of_le htt' (le_enveloppeSci (hz.mono fun _ h => h.le))

end EnveloppeSci

omit [NormedSpace ℝ E] in
/-- Le sur-graphe de l'enveloppe s.c.i. est l'adhérence du sur-graphe. -/
theorem surGraphe_enveloppeSci (f : E → EReal) :
    {p : E × ℝ | enveloppeSci f p.1 ≤ p.2} = closure {p : E × ℝ | f p.1 ≤ p.2} := by
  apply Subset.antisymm
  · rintro ⟨x, t⟩ hxt
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hlt : enveloppeSci f x < ((t + ε / 2 : ℝ) : EReal) :=
      lt_of_le_of_lt hxt (EReal.coe_lt_coe_iff.mpr (by linarith))
    obtain ⟨y, hy1, hy2⟩ := ((frequently_lt_of_enveloppeSci_lt hlt).and_eventually
      (Metric.ball_mem_nhds x hε)).exists
    refine ⟨(y, t + ε / 2), hy1.le, ?_⟩
    rw [Prod.dist_eq, Real.dist_eq, sup_lt_iff, dist_comm]
    refine ⟨hy2, ?_⟩
    rw [show t - (t + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos (by positivity)]
    linarith
  · refine closure_minimal (fun p hp => (enveloppeSci_le f p.1).trans hp) ?_
    exact (lowerSemicontinuous_iff_isClosed_surGraphe _).mp
      (lowerSemicontinuous_enveloppeSci f)

theorem conjuguee_enveloppeSci (f : E → EReal) : conjuguee (enveloppeSci f) = conjuguee f := by
  funext φ
  refine le_antisymm (iSup_le fun x => ?_) (conjuguee_anti (enveloppeSci_le f) φ)
  by_contra hcon
  push Not at hcon
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨r', hr1', hr2'⟩ := EReal.lt_iff_exists_real_btwn.mp hr2
  have hrr : r < r' := EReal.coe_lt_coe_iff.mp hr1'
  rw [coe_lt_coe_sub_iff] at hr2'
  have hcont : ∀ᶠ y in 𝓝 x, φ x - (r' - r) < φ y :=
    φ.continuous.continuousAt.eventually (lt_mem_nhds (by linarith))
  obtain ⟨y, hy1, hy2⟩ := ((frequently_lt_of_enveloppeSci_lt hr2').and_eventually hcont).exists
  have : (r : EReal) < ((φ y : ℝ) : EReal) - f y := by
    rw [coe_lt_coe_sub_iff]
    exact lt_trans hy1 (EReal.coe_lt_coe_iff.mpr (by linarith))
  exact absurd (lt_of_lt_of_le this (le_conjuguee f φ y)) (not_lt.mpr hr1.le)

/-- **Lemme `lem:cvxSciAlt` (Alternative pour l'enveloppe s.c.i. d'une fonction convexe).**
Soit `f : E → ]-∞, ∞]` convexe sur un evn, et `g(x) := liminf_{y → x} f(y)` son enveloppe s.c.i.
Alors : (a) `g : E → ]-∞, ∞]` est convexe, s.c.i., et `g* = f*` ; ou bien (b) `g` ne prend que
les valeurs `±∞`, et `{g = -∞} = adh(Dom f)`. -/
theorem lem_cvxSciAlt (f : E → EReal) (hbot : ∀ x, f x ≠ ⊥) (hc : ConvexeEtendue f) :
    ((∀ x, enveloppeSci f x ≠ ⊥) ∧ ConvexeEtendue (enveloppeSci f) ∧
      LowerSemicontinuous (enveloppeSci f) ∧ conjuguee (enveloppeSci f) = conjuguee f) ∨
    ((∀ x, enveloppeSci f x = ⊥ ∨ enveloppeSci f x = ⊤) ∧
      {x | enveloppeSci f x = ⊥} = closure (domaine f)) := by
  by_cases hb : ∀ x, enveloppeSci f x ≠ ⊥
  · refine Or.inl ⟨hb, ?_, lowerSemicontinuous_enveloppeSci f, conjuguee_enveloppeSci f⟩
    rw [ConvexeEtendue, surGraphe_enveloppeSci]
    exact hc.closure
  push Not at hb
  obtain ⟨xs, hxs⟩ := hb
  -- hors de `adh(Dom f)`, `g = +∞`
  have hA : ∀ x ∉ closure (domaine f), enveloppeSci f x = ⊤ := by
    intro x hx
    refine top_le_iff.mp (le_enveloppeSci ?_)
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
    by_contra hlt
    exact hy (subset_closure (lt_of_not_ge hlt))
  -- sur `adh(Dom f)`, `g = -∞`
  have hB : ∀ y ∈ closure (domaine f), enveloppeSci f y = ⊥ := by
    intro ys hys
    refine (EReal.eq_bot_iff_forall_lt _).mpr fun t => ?_
    refine lt_of_le_of_lt (liminf_le_of_frequently_le' (x := ((t - 1 : ℝ) : EReal)) ?_)
      (EReal.coe_lt_coe_iff.mpr (sub_one_lt t))
    refine Filter.frequently_iff.mpr fun {V} hV => ?_
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hys (ε / 2) (by positivity)
    obtain ⟨b, hb⟩ := exists_coe_eq hbot (hy : f y < ⊤).ne
    set R := ‖xs - y‖ + 1 with hR
    have hRpos : 0 < R := by positivity
    set s := min (1 / 2) (ε / (4 * R)) with hs
    have hspos : 0 < s := lt_min (by norm_num) (by positivity)
    have hs1 : s ≤ 1 / 2 := min_le_left _ _
    have hsR : s * R ≤ ε / 4 := by
      have : s ≤ ε / (4 * R) := min_le_right _ _
      calc s * R ≤ ε / (4 * R) * R := mul_le_mul_of_nonneg_right this hRpos.le
        _ = ε / 4 := by field_simp
    set T := (t - 1 - (1 - s) * b) / s with hT
    have hxs' : enveloppeSci f xs < (T : EReal) := by rw [hxs]; exact EReal.bot_lt_coe T
    obtain ⟨x, hx1, hx2⟩ := ((frequently_lt_of_enveloppeSci_lt hxs').and_eventually
      (Metric.ball_mem_nhds xs one_pos)).exists
    obtain ⟨T', hT'⟩ := exists_coe_eq hbot (ne_top_of_lt hx1)
    rw [hT', EReal.coe_lt_coe_iff] at hx1
    refine ⟨(1 - s) • y + s • x, hεV ?_, ?_⟩
    · have hxy : ‖x - y‖ < R := by
        calc ‖x - y‖ = ‖(x - xs) + (xs - y)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖x - xs‖ + ‖xs - y‖ := norm_add_le _ _
          _ < 1 + ‖xs - y‖ := by
              rw [← dist_eq_norm]
              linarith [Metric.mem_ball.mp hx2]
          _ = R := by ring
      have e : (1 - s) • y + s • x - ys = s • (x - y) + (y - ys) := by module
      rw [Metric.mem_ball, dist_eq_norm, e]
      calc ‖s • (x - y) + (y - ys)‖ ≤ ‖s • (x - y)‖ + ‖y - ys‖ := norm_add_le _ _
        _ = s * ‖x - y‖ + dist y ys := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, dist_eq_norm]
        _ < ε := by
            rw [dist_comm]
            nlinarith [mul_le_mul_of_nonneg_left hxy.le hspos.le]
    · have := hc.le_comb (x := y) (y := x) (a := 1 - s) (b := s) hb.le hT'.le (by linarith)
        hspos.le (by ring)
      refine this.trans (EReal.coe_le_coe_iff.mpr ?_)
      have hsT : s * T = t - 1 - (1 - s) * b := by rw [hT]; field_simp
      nlinarith [mul_lt_mul_of_pos_left hx1 hspos]
  refine Or.inr ⟨fun x => ?_, ?_⟩
  · by_cases hx : x ∈ closure (domaine f)
    · exact Or.inl (hB x hx)
    · exact Or.inr (hA x hx)
  · ext x
    refine ⟨fun hx => ?_, hB x⟩
    by_contra hx'
    rw [mem_ofPred_eq, hA x hx'] at hx
    exact top_ne_bot hx

/-! ### Théorème `th:FenchelRockafellar` -/

/-- Une somme `a + b < t` de deux éléments de `]-∞, ∞]` est une somme de réels. -/
theorem ereal_add_lt_split {a b : EReal} (ha : a ≠ ⊥) (hb : b ≠ ⊥) {t : ℝ}
    (h : a + b < t) : ∃ s₁ s₂ : ℝ, a = s₁ ∧ b = s₂ ∧ s₁ + s₂ < t := by
  have hat : a ≠ ⊤ := fun h' => by
    rw [h', EReal.top_add_of_ne_bot hb] at h
    exact not_top_lt h
  have hbt : b ≠ ⊤ := fun h' => by
    rw [h', EReal.add_top_of_ne_bot ha] at h
    exact not_top_lt h
  lift a to ℝ using ⟨hat, ha⟩ with s₁
  lift b to ℝ using ⟨hbt, hb⟩ with s₂
  exact ⟨s₁, s₂, rfl, rfl, by exact_mod_cast h⟩

theorem comb_lt {a₁ a₂ u v u' v' : ℝ} (ha : 0 ≤ a₁) (hb : 0 ≤ a₂) (hab : a₁ + a₂ = 1)
    (h : u < v) (h' : u' < v') : a₁ * u + a₂ * u' < a₁ * v + a₂ * v' := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have : a₂ = 1 := by linarith
    subst this
    linarith
  · nlinarith [mul_lt_mul_of_pos_left h hpos, mul_le_mul_of_nonneg_left h'.le hb]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Dualité faible : `-f*(-Aᵀy) - g*(y) ≤ f(x) + g(Ax)`. -/
theorem fenchelRockafellar_faible (A : E →L[ℝ] F) {f : E → EReal} {g : F → EReal}
    (hfb : ∀ x, f x ≠ ⊥) (hgb : ∀ y, g y ≠ ⊥) (y : StrongDual ℝ F) (x : E) :
    -conjuguee f (-(y.comp A)) - conjuguee g y ≤ f x + g (A x) := by
  by_cases hft : f x = ⊤
  · rw [hft, EReal.top_add_of_ne_bot (hgb _)]
    exact le_top
  by_cases hgt : g (A x) = ⊤
  · rw [hgt, EReal.add_top_of_ne_bot (hfb _)]
    exact le_top
  obtain ⟨a, ha⟩ := exists_coe_eq hfb hft
  obtain ⟨b, hb⟩ := exists_coe_eq hgb hgt
  have h1 : ((-y (A x) - a : ℝ) : EReal) ≤ conjuguee f (-(y.comp A)) := by
    have := le_conjuguee f (-(y.comp A)) x
    rwa [ha, ← EReal.coe_sub, neg_apply,
      ContinuousLinearMap.comp_apply] at this
  have h2 : ((y (A x) - b : ℝ) : EReal) ≤ conjuguee g y := by
    have := le_conjuguee g y (A x)
    rwa [hb, ← EReal.coe_sub] at this
  refine (EReal.sub_le_sub (EReal.neg_le_neg_iff.mpr h1) h2).trans (le_of_eq ?_)
  rw [ha, hb, ← EReal.coe_neg, ← EReal.coe_sub, ← EReal.coe_add]
  congr 1
  ring

/-- **Thm. `th:FenchelRockafellar` (Fenchel-Rockafellar).** Soient `E` et `F` des Banach, et
`A ∈ L(E, F)`. Soient `f : E → ]-∞, ∞]` et `g : F → ]-∞, ∞]` convexes, s.c.i., et telles que
`(A Dom f) ∩ int(Dom g) ≠ ∅`. Alors
`sup_{y ∈ F*} -f*(-Aᵀy) - g*(y) = inf_{x ∈ E} f(x) + g(Ax)`, avec `Aᵀy = y ∘ A`.
Remarque : la preuve formelle sépare directement le point `(0, β)` du sur-graphe strict de
`u ↦ inf_x f(x) + g(Ax + u)` (Hahn-Banach), au lieu de passer par le `lem:cvxSciAlt` ; la
s.c.i. de `f` et la complétude de `E` n'y sont pas utilisées. -/
theorem th_FenchelRockafellar [CompleteSpace E] [CompleteSpace F] (A : E →L[ℝ] F)
    (f : E → EReal) (g : F → EReal) (hfb : ∀ x, f x ≠ ⊥) (hgb : ∀ y, g y ≠ ⊥)
    (hfc : ConvexeEtendue f) (hgc : ConvexeEtendue g) (_hfl : LowerSemicontinuous f)
    (hgl : LowerSemicontinuous g) (hdom : ∃ x ∈ domaine f, A x ∈ interior (domaine g)) :
    ⨆ y : StrongDual ℝ F, -conjuguee f (-(y.comp A)) - conjuguee g y =
      ⨅ x, f x + g (A x) := by
  refine le_antisymm (iSup_le fun y => le_iInf fun x => fenchelRockafellar_faible A hfb hgb y x)
    ?_
  obtain ⟨x₁, hx₁, hAx₁⟩ := hdom
  have hx₁' : f x₁ < ⊤ := hx₁
  rcases eq_bot_or_bot_lt (⨅ x, f x + g (A x)) with hbot | hβbot
  · rw [hbot]
    exact bot_le
  have hgA : g (A x₁) < ⊤ := (interior_subset (s := domaine g) hAx₁ :)
  have hβtop : (⨅ x, f x + g (A x)) ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.add_lt_top hx₁'.ne hgA.ne).ne (iInf_le _ x₁)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, (⨅ x, f x + g (A x)) = b :=
    ⟨_, (EReal.coe_toReal hβtop hβbot.ne').symm⟩
  obtain ⟨c, hc⟩ := exists_coe_eq hfb hx₁'.ne
  obtain ⟨ρ, hρ, M, hM⟩ := majoration_locale hgb hgc hgl hAx₁
  set S : Set (F × ℝ) := {p | ∃ x, f x + g (A x + p.1) < p.2} with hS
  -- convexité de `S`
  have hSconv : Convex ℝ S := by
    rintro p ⟨xp, hxp⟩ q ⟨xq, hxq⟩ a₁ a₂ ha hb' hab
    obtain ⟨s₁, s₂, h₁, h₂, h₁₂⟩ := ereal_add_lt_split (hfb _) (hgb _) hxp
    obtain ⟨s₁', s₂', h₁', h₂', h₁₂'⟩ := ereal_add_lt_split (hfb _) (hgb _) hxq
    refine ⟨a₁ • xp + a₂ • xq, ?_⟩
    have hf' := hfc.le_comb h₁.le h₁'.le ha hb' hab
    have hg' := hgc.le_comb h₂.le h₂'.le ha hb' hab
    have e : A (a₁ • xp + a₂ • xq) + (a₁ • p + a₂ • q).1 =
        a₁ • (A xp + p.1) + a₂ • (A xq + q.1) := by
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst]
      module
    rw [e]
    refine lt_of_le_of_lt (add_le_add hf' hg') ?_
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have := comb_lt ha hb' hab h₁₂ h₁₂'
    linarith
  -- les points `(u, t)` avec `‖u‖ < ρ` et `t > c + M` sont dans `S`
  have hSball : ∀ u ∈ Metric.ball (0 : F) ρ, ∀ t : ℝ, c + M < t → (u, t) ∈ S := by
    intro u hu t ht
    refine ⟨x₁, ?_⟩
    have hgu : g (A x₁ + u) ≤ M := hM _ (by
      rwa [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, ← dist_zero_right])
    rw [hc]
    refine lt_of_le_of_lt (add_le_add le_rfl hgu) ?_
    rw [← EReal.coe_add, EReal.coe_lt_coe_iff]
    exact ht
  have hint : (interior S).Nonempty := by
    refine ⟨(0, c + M + 1), mem_interior_iff_mem_nhds.mpr (mem_of_superset
      (prod_mem_nhds (Metric.ball_mem_nhds 0 hρ) (Ioi_mem_nhds (lt_add_one (c + M))))
      fun p hp => hSball p.1 hp.1 p.2 hp.2)⟩
  have hnot : ((0 : F), b) ∉ interior S := by
    intro h
    obtain ⟨x, hx⟩ := interior_subset h
    rw [add_zero] at hx
    have := iInf_le (fun x => f x + g (A x)) x
    rw [hb] at this
    exact absurd hx (not_lt.mpr this)
  obtain ⟨L, hL0, hLmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hSconv hnot hint
  set ψ := L.comp (ContinuousLinearMap.inl ℝ F ℝ) with hψ
  set l := L (0, 1) with hldef
  have h : ∀ (u : F) (t : ℝ), (u, t) ∈ S → ψ u + t * l ≤ b * l := by
    intro u t hut
    have e2 : L (0, b) = b * l := by rw [clm_prod_apply, map_zero, zero_add]
    have := hLmax (u, t) hut
    rwa [e2, clm_prod_apply] at this
  have hl0 : l ≤ 0 := by
    have hlt : (⨅ x, f x + g (A x)) < ((b + 1 : ℝ) : EReal) := by
      rw [hb, EReal.coe_lt_coe_iff]
      linarith
    rw [iInf_lt_iff] at hlt
    obtain ⟨x, hx⟩ := hlt
    have := h 0 (b + 1) ⟨x, by rwa [add_zero]⟩
    rw [map_zero] at this
    linarith
  have hlneg : l < 0 := by
    refine lt_of_le_of_ne hl0 fun hzero => hL0 ?_
    have hloc : ∀ u ∈ Metric.ball (0 : F) ρ, ψ u ≤ ψ 0 := by
      intro u hu
      have := h u (c + M + 1) (hSball u hu _ (lt_add_one _))
      rw [hzero, mul_zero, mul_zero, add_zero] at this
      rwa [map_zero]
    have hψ0 := clm_eq_zero_of_local_max ψ hρ hloc
    refine ContinuousLinearMap.ext fun p => ?_
    rw [show p = (p.1, p.2) from rfl, clm_prod_apply, ← hψ, hψ0, ← hldef, hzero]
    simp
  set y : StrongDual ℝ F := (-l⁻¹) • ψ with hy
  have hyw : ∀ w, y w = -(ψ w / l) := by
    intro w
    rw [hy, smul_apply, smul_eq_mul, div_eq_inv_mul, neg_mul]
  -- inégalité clé : `b + y(v - Ax) ≤ f(x) + g(v)`
  have hkey : ∀ (x : E) (v : F) (s₁ s₂ : ℝ), f x = s₁ → g v = s₂ →
      b + y (v - A x) ≤ s₁ + s₂ := by
    intro x v s₁ s₂ h₁ h₂
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hmem : (v - A x, s₁ + s₂ + δ) ∈ S := ⟨x, by
      rw [add_sub_cancel, h₁, h₂, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      linarith⟩
    have h3 := h _ _ hmem
    rw [hyw]
    set q := ψ (v - A x) / l with hq
    have hql : ψ (v - A x) = q * l := by rw [hq, div_mul_cancel₀ _ hlneg.ne]
    rw [hql] at h3
    by_contra hcon
    push Not at hcon
    have := mul_pos_of_neg_of_neg (show q + (s₁ + s₂ + δ) - b < 0 by linarith) hlneg
    nlinarith
  set K := conjuguee f (-(y.comp A)) with hK
  have hKle : ∀ (v : F) (d : ℝ), g v = d → K ≤ ((-b - y v + d : ℝ) : EReal) := by
    intro v d hd
    refine iSup_le fun x => ?_
    by_cases hft : f x = ⊤
    · rw [hft, EReal.sub_top]
      exact bot_le
    obtain ⟨s₁, hs₁⟩ := exists_coe_eq hfb hft
    rw [hs₁, coe_sub_le_coe_iff, EReal.coe_le_coe_iff, neg_apply,
      ContinuousLinearMap.comp_apply]
    have := hkey x v s₁ d hs₁ hd
    rw [map_sub] at this
    linarith
  obtain ⟨d₁, hd₁⟩ := exists_coe_eq hgb hgA.ne
  have hKbot : K ≠ ⊥ := (lem_FenchelPropre f ⟨hfb, x₁, hx₁⟩).1 _
  have hKtop : K ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hKle _ _ hd₁)
  lift K to ℝ using ⟨hKtop, hKbot⟩ with k hk
  have hG : conjuguee g y ≤ ((-b - k : ℝ) : EReal) := by
    refine iSup_le fun v => ?_
    by_cases hgt : g v = ⊤
    · rw [hgt, EReal.sub_top]
      exact bot_le
    obtain ⟨s₂, hs₂⟩ := exists_coe_eq hgb hgt
    rw [hs₂, coe_sub_le_coe_iff, EReal.coe_le_coe_iff]
    have := hKle v s₂ hs₂
    rw [EReal.coe_le_coe_iff] at this
    linarith
  rw [hb]
  refine le_iSup_of_le y ?_
  rw [← hK]
  refine le_trans (le_of_eq ?_) (EReal.sub_le_sub le_rfl hG)
  rw [← EReal.coe_neg, ← EReal.coe_sub]
  congr 1
  ring

end M1Analyse
