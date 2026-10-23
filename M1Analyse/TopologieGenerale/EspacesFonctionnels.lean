/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# §1.4 Exemples d'espaces fonctionnels (`subsec:evtlc`)

Source : `Include/TopologieGenerale.tex`, seconde sous-sous-section « Exemples d'espaces
fonctionnels » de la sous-section `subsec:evtlc` (la sous-sous-section elle-même n'a pas de
label).

On travaille sur `ℝ^d = EuclideanSpace ℝ (Fin d)`. Les objets du cours sont ceux de Mathlib
lorsqu'ils existent : classe de Schwartz `𝓢(ℝ^d, F)` (`SchwartzMap`), fonctions test
`𝓓(Ω, F)` (`TestFunction`, munies de la topologie limite inductive), espaces `𝓓_K`
(`ContDiffMapSupportedIn`), `L^p` local via `MemLp` sur les compacts. Mathlib utilise les normes
`‖D^j f(x)‖` des différentielles itérées plutôt que les dérivées partielles `∂_α f(x)` ; on
introduit les dérivées partielles itérées `derivPartielle` et on montre que les deux familles de
contrôles sont équivalentes (`norm_derivPartielle_le`, `norm_iteratedFDeriv_le_sum`).
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal ContDiff Distributions SchwartzMap

namespace M1Analyse

variable {d : ℕ}

/-! ### Suites exhaustives de compacts -/

/-- Une suite `(K_n)` de parties de `Ω` est une *suite exhaustive de compacts* de `Ω`
(`eqdef:exhaustive_compacts`) si chaque `K_n` est compact, si `⋃_n K_n = Ω`, et si
`K_n ⊆ int(K_{n+1})` pour tout `n`. (Pour `Ω = X` tout entier, c'est la notion Mathlib
`CompactExhaustion X`, cf. `isSuiteExhaustive_compactExhaustion`.) -/
def IsSuiteExhaustive {X : Type*} [TopologicalSpace X] (Ω : Set X) (K : ℕ → Set X) : Prop :=
  (∀ n, IsCompact (K n)) ∧ (⋃ n, K n) = Ω ∧ ∀ n, K n ⊆ interior (K (n + 1))

/-- Une `CompactExhaustion` de Mathlib est une suite exhaustive de compacts de l'espace entier. -/
theorem isSuiteExhaustive_compactExhaustion {X : Type*} [TopologicalSpace X]
    (K : CompactExhaustion X) : IsSuiteExhaustive univ K :=
  ⟨K.isCompact, K.iUnion_eq, K.subset_interior_succ⟩

/-- **Prop. `prop:exhaustComp` (Suite exhaustive de compacts).** Tout ouvert `Ω ⊆ ℝ^d` admet
une suite exhaustive de compacts `(K_n)` : `⋃_n K_n = Ω` et `K_n ⊂⊂ int(K_{n+1})`
(`eqdef:exhaustive_compacts`). (Preuve via `CompactExhaustion.choice` sur le sous-espace `Ω`,
et non via la suite explicite du cours.) -/
theorem prop_exhaustComp {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω) :
    ∃ K : ℕ → Set (EuclideanSpace ℝ (Fin d)), IsSuiteExhaustive Ω K := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let C := CompactExhaustion.choice Ω
  refine ⟨fun n => Subtype.val '' C n, fun n => (C.isCompact n).image continuous_subtype_val, ?_,
    fun n => ?_⟩
  · rw [← image_iUnion, C.iUnion_eq, image_univ, Subtype.range_coe]
  · calc Subtype.val '' C n ⊆ Subtype.val '' interior (C (n + 1)) :=
          image_mono (C.subset_interior_succ n)
      _ ⊆ interior (Subtype.val '' C (n + 1)) :=
        hΩ.isOpenEmbedding_subtypeVal.isOpenMap.image_interior_subset _

/-- Propriété utilisée implicitement dans le cours : tout compact `K ⊆ Ω` est contenu dans l'un
des `K_n` d'une suite exhaustive. -/
theorem IsSuiteExhaustive.exists_subset {X : Type*} [TopologicalSpace X] {Ω : Set X}
    {K : ℕ → Set X} (hK : IsSuiteExhaustive Ω K) {L : Set X} (hL : IsCompact L)
    (hLΩ : L ⊆ Ω) : ∃ n, L ⊆ K n := by
  have hmono : Monotone K :=
    monotone_nat_of_le_succ fun n => (hK.2.2 n).trans interior_subset
  have hcov : L ⊆ ⋃ n, interior (K (n + 1)) := by
    intro x hx
    rw [← hK.2.1] at hLΩ
    obtain ⟨n, hn⟩ := mem_iUnion.1 (hLΩ hx)
    exact mem_iUnion.2 ⟨n, hK.2.2 n hn⟩
  obtain ⟨n, hn⟩ := hL.elim_directed_cover _ (fun _ => isOpen_interior) hcov
    (Monotone.directed_le fun a b hab => interior_mono (hmono (Nat.succ_le_succ hab)))
  exact ⟨n + 1, hn.trans interior_subset⟩

/-! ### `L^p_loc` -/

section Lploc

variable {F : Type*} [NormedAddCommGroup F]

/-- **Déf. `def:lploc` (Evtlcs `L^p_loc`).** Soit `(K_n)` une suite exhaustive de compacts de
l'ouvert `Ω ⊆ ℝ^d`. Les semi-normes `|f|_n = ‖f‖_{L^p(K_n)}` sont toutes finies (pour `f`
mesurable) si et seulement si `f` est dans `L^p(K)` pour tout compact `K ⊆ Ω` ; en particulier
l'ensemble `L^p_loc(Ω)` ne dépend pas de la suite exhaustive choisie.
Remarque : on énonce seulement la condition d'appartenance ; l'espace quotient `L^p_loc(Ω)` et
sa topologie n'existent pas dans Mathlib. L'énoncé vaut pour tout `p ∈ [0, ∞]`. -/
theorem def_lploc {Ω : Set (EuclideanSpace ℝ (Fin d))} {K : ℕ → Set (EuclideanSpace ℝ (Fin d))}
    (hK : IsSuiteExhaustive Ω K) (p : ℝ≥0∞) (f : EuclideanSpace ℝ (Fin d) → F) :
    (∀ n, MemLp f p (volume.restrict (K n))) ↔
      ∀ L, IsCompact L → L ⊆ Ω → MemLp f p (volume.restrict L) := by
  constructor
  · intro h L hL hLΩ
    obtain ⟨n, hn⟩ := hK.exists_subset hL hLΩ
    exact (h n).mono_measure (Measure.restrict_mono hn le_rfl)
  · intro h n
    exact h _ (hK.1 n) (hK.2.1 ▸ subset_iUnion K n)

/-- **Déf. `def:lploc`, cas `p = 1`.** Pour `p = 1`, `L^1_loc(Ω)` est la notion Mathlib
`LocallyIntegrableOn f Ω` (intégrabilité sur chaque `K_n`). -/
theorem def_lploc_un {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin d))} (hK : IsSuiteExhaustive Ω K)
    (f : EuclideanSpace ℝ (Fin d) → F) :
    (∀ n, MemLp f 1 (volume.restrict (K n))) ↔ LocallyIntegrableOn f Ω := by
  rw [def_lploc hK, locallyIntegrableOn_iff hΩ.isLocallyClosed]
  simp only [memLp_one_iff_integrable]
  exact ⟨fun h L hLΩ hL => h L hL hLΩ, fun h L hL hLΩ => h L hLΩ hL⟩

end Lploc

/-! ### Dérivées partielles itérées -/

section DerivPartielle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Dérivée partielle itérée `∂_{w_1} ⋯ ∂_{w_j} f(x)` dans les directions `e_{w_1}, …, e_{w_j}`
de la base canonique de `ℝ^d`, définie comme `D^j f(x)(e_{w_1}, …, e_{w_j})`.
Remarque : le cours indexe les dérivées partielles par des multi-indices `α ∈ ℕ^d` ; pour `f` de
classe `C^j`, le lemme de Schwarz donne `∂_w f = ∂_α f` où `α_i = #{k | w_k = i}`, de sorte que
les maxima sur `|α|_1 ≤ k` du cours coïncident avec les maxima sur les mots `w` de longueur
`≤ k` utilisés ici. -/
noncomputable def derivPartielle (j : ℕ) (w : Fin j → Fin d)
    (f : EuclideanSpace ℝ (Fin d) → F) (x : EuclideanSpace ℝ (Fin d)) : F :=
  iteratedFDeriv ℝ j f x (fun i => EuclideanSpace.single (w i) (1 : ℝ))

/-- Une dérivée partielle est contrôlée par la norme de la différentielle itérée. -/
theorem norm_derivPartielle_le (j : ℕ) (w : Fin j → Fin d)
    (f : EuclideanSpace ℝ (Fin d) → F) (x : EuclideanSpace ℝ (Fin d)) :
    ‖derivPartielle j w f x‖ ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  refine ((iteratedFDeriv ℝ j f x).le_opNorm _).trans ?_
  simp

/-- La norme d'une application multilinéaire sur `ℝ^d` est contrôlée par ses valeurs sur la
base canonique. -/
theorem norm_multilinear_le_sum {j : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin j => EuclideanSpace ℝ (Fin d)) F) :
    ‖M‖ ≤ ∑ w : Fin j → Fin d, ‖M (fun i => EuclideanSpace.single (w i) (1 : ℝ))‖ := by
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = fun i => ∑ k, v i k • EuclideanSpace.single k (1 : ℝ) := by
    funext i
    ext m
    simp [Pi.single_apply]
  have hM : M v = ∑ w : Fin j → Fin d,
      (∏ i, v i (w i)) • M (fun i => EuclideanSpace.single (w i) (1 : ℝ)) := by
    conv_lhs => rw [hv]
    rw [M.map_sum]
    congr 1; ext w
    rw [M.map_smul_univ]
  rw [hM, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_smul, norm_prod, mul_comm]
  gcongr with i
  exact PiLp.norm_apply_le (v i) (w i)

/-- La norme de la différentielle itérée est contrôlée par la somme des dérivées partielles. -/
theorem norm_iteratedFDeriv_le_sum (j : ℕ) (f : EuclideanSpace ℝ (Fin d) → F)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ ∑ w : Fin j → Fin d, ‖derivPartielle j w f x‖ :=
  norm_multilinear_le_sum _

end DerivPartielle

/-! ### Classe de Schwartz -/

section Schwartz

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Le poids `(1 + t²)^{n/2}` vaut `(√(1 + t²))^n`. -/
lemma poids_eq_sqrt_pow (t : ℝ) (n : ℕ) :
    (1 + t ^ 2) ^ ((n : ℝ) / 2) = √(1 + t ^ 2) ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
  ring_nf

lemma sqrt_one_add_sq_le {t : ℝ} (ht : 0 ≤ t) : √(1 + t ^ 2) ≤ 1 + t := by
  calc √(1 + t ^ 2) ≤ √((1 + t) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = 1 + t := Real.sqrt_sq (by linarith)

lemma le_sqrt_one_add_sq {t : ℝ} (ht : 0 ≤ t) : t ≤ √(1 + t ^ 2) := by
  calc t = |t| := (abs_of_nonneg ht).symm
    _ ≤ √(1 + t ^ 2) := Real.abs_le_sqrt (by linarith)

/-- **Déf. `def:classeSchwartz` (Classe de Schwartz).** Une fonction `f : ℝ^d → F` appartient à
la classe de Schwartz `𝓢(ℝ^d, F)` de Mathlib si et seulement si elle est `C^∞` et toutes les
semi-normes du cours `|f|_{n,α} = sup_x (1 + |x|²)^{n/2} |∂_α f(x)|` sont finies.
Remarques : (1) les dérivées partielles `∂_α` sont indexées par des mots `w`
(cf. `derivPartielle`) ; (2) Mathlib définit `𝓢` via les bornes `‖x‖^k ‖D^n f(x)‖ ≤ C`, et
munit `𝓢` de la topologie des semi-normes associées (`SchwartzMap.seminorm`) ; l'équivalence
des deux familles de semi-normes (donc des topologies) n'est pas formalisée ici ; (3) on
autorise des valeurs dans un evn réel `F` quelconque (le cours : `F = ℝ` ou `ℂ`). -/
theorem def_classeSchwartz (f : EuclideanSpace ℝ (Fin d) → F) :
    (∃ g : 𝓢(EuclideanSpace ℝ (Fin d), F), ⇑g = f) ↔
      ContDiff ℝ ∞ f ∧ ∀ (n j : ℕ) (w : Fin j → Fin d), ∃ C : ℝ, ∀ x,
        (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) * ‖derivPartielle j w f x‖ ≤ C := by
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.smooth ⊤, fun n j w => ⟨2 ^ n * (Finset.Iic (n, j)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g, fun x => ?_⟩⟩
    calc (1 + ‖x‖ ^ 2) ^ ((n : ℝ) / 2) * ‖derivPartielle j w g x‖
        ≤ (1 + ‖x‖) ^ n * ‖iteratedFDeriv ℝ j g x‖ := by
          rw [poids_eq_sqrt_pow]
          gcongr
          · exact sqrt_one_add_sq_le (norm_nonneg x)
          · exact norm_derivPartielle_le j w g x
      _ ≤ _ := SchwartzMap.one_add_le_sup_seminorm_apply (m := (n, j)) le_rfl le_rfl g x
  · rintro ⟨hf, hb⟩
    choose C hC using hb
    refine ⟨⟨f, hf, fun k n => ⟨∑ w : Fin n → Fin d, C k n w, fun x => ?_⟩⟩, rfl⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
        ≤ (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) * ∑ w : Fin n → Fin d, ‖derivPartielle n w f x‖ := by
          rw [poids_eq_sqrt_pow]
          gcongr
          · exact le_sqrt_one_add_sq (norm_nonneg x)
          · exact norm_iteratedFDeriv_le_sum n f x
      _ = ∑ w : Fin n → Fin d, (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) * ‖derivPartielle n w f x‖ :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ w : Fin n → Fin d, C k n w := Finset.sum_le_sum fun w _ => hC k n w x

end Schwartz

/-! ### Espaces `C^k(Ω)` -/

section ContNonBornee

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Déf. `def:cont_nonbornee` (Evtlcs `C^k(Ω)` et `C^∞(Ω)`).** Soit `Ω ⊆ ℝ^d` ouvert, muni
d'une suite exhaustive de compacts `(K_n)`, et `k ∈ ℕ ∪ {∞}`. Pour `f ∈ C^k(Ω)`, les
semi-normes `|f|_{n,α} = ‖∂_α f‖_{L^∞(K_n)}`, `|α|_1 ≤ k`, sont finies.
Remarque : seule la finitude des semi-normes est formalisée ; Mathlib ne possède pas l'espace
`C^k(Ω)` muni de cette topologie (dérivées partielles indexées par des mots, cf.
`derivPartielle`). -/
theorem def_cont_nonbornee {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin d))} (hK : IsSuiteExhaustive Ω K) {k : ℕ∞}
    {f : EuclideanSpace ℝ (Fin d) → F} (hf : ContDiffOn ℝ k f Ω) (n j : ℕ) (hj : (j : ℕ∞) ≤ k)
    (w : Fin j → Fin d) : ∃ C, ∀ x ∈ K n, ‖derivPartielle j w f x‖ ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ j f) Ω :=
    (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hΩ.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen j hΩ).symm
  obtain ⟨C, hC⟩ := (hK.1 n).exists_bound_of_continuousOn
    (hcont.mono (hK.2.1 ▸ subset_iUnion K n))
  exact ⟨C, fun x hx => (norm_derivPartielle_le j w f x).trans (hC x hx)⟩

end ContNonBornee

/-! ### Fonctions test et distributions -/

section Distribution

/-- La semi-norme du cours `max_{|α|_1 ≤ n} ‖∂_α f‖_{L^∞(K)}`, écrite comme un supremum sur
`x ∈ K` et sur les mots `w` de longueur `j ≤ n` (cf. `derivPartielle`). -/
noncomputable def normeK (K : Set (EuclideanSpace ℝ (Fin d))) (n : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ⨆ x : K, ⨆ j : Fin (n + 1), ⨆ w : Fin j → Fin d, ‖derivPartielle j w f x‖

lemma normeK_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) (n : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : 0 ≤ normeK K n f :=
  Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => norm_nonneg _

lemma normeK_le {K : Set (EuclideanSpace ℝ (Fin d))} {n : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ K, ∀ j ≤ n, ∀ w : Fin j → Fin d, ‖derivPartielle j w f x‖ ≤ c) :
    normeK K n f ≤ c :=
  Real.iSup_le (fun x => Real.iSup_le (fun j => Real.iSup_le
    (fun w => h x x.2 j (Nat.lt_succ_iff.1 j.2) w) hc) hc) hc

lemma le_normeK {K : Set (EuclideanSpace ℝ (Fin d))} {n : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (h : ∀ x ∈ K, ∀ j ≤ n, ∀ w : Fin j → Fin d, ‖derivPartielle j w f x‖ ≤ c)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ K) {j : ℕ} (hj : j ≤ n) (w : Fin j → Fin d) :
    ‖derivPartielle j w f x‖ ≤ normeK K n f := by
  have hc : 0 ≤ max c 0 := le_max_right _ _
  have h' : ∀ x ∈ K, ∀ j ≤ n, ∀ w : Fin j → Fin d, ‖derivPartielle j w f x‖ ≤ max c 0 :=
    fun x hx j hj w => (h x hx j hj w).trans (le_max_left _ _)
  have b1 : ∀ (y : K) (i : Fin (n + 1)),
      BddAbove (range fun w : Fin i → Fin d => ‖derivPartielle i w f y‖) := by
    rintro y i
    exact ⟨max c 0, by rintro _ ⟨w, rfl⟩; exact h' y y.2 i (Nat.lt_succ_iff.1 i.2) w⟩
  have b2 : ∀ y : K, BddAbove (range fun i : Fin (n + 1) =>
      ⨆ w : Fin i → Fin d, ‖derivPartielle i w f y‖) := by
    intro y
    refine ⟨max c 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact Real.iSup_le (fun w => h' y y.2 i (Nat.lt_succ_iff.1 i.2) w) hc
  have b3 : BddAbove (range fun y : K => ⨆ i : Fin (n + 1),
      ⨆ w : Fin i → Fin d, ‖derivPartielle i w f y‖) := by
    refine ⟨max c 0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.iSup_le (fun i => Real.iSup_le
      (fun w => h' y y.2 i (Nat.lt_succ_iff.1 i.2) w) hc) hc
  exact le_ciSup_of_le b3 ⟨x, hx⟩ (le_ciSup_of_le (b2 ⟨x, hx⟩) ⟨j, Nat.lt_succ_of_le hj⟩
    (le_ciSup (b1 ⟨x, hx⟩ ⟨j, Nat.lt_succ_of_le hj⟩) w))

variable {K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d))}

/-- Pour `g ∈ 𝓓_K`, la semi-norme du cours est majorée par le max des semi-normes de Mathlib. -/
lemma normeK_le_sup_seminorm (n : ℕ) (g : 𝓓_{K}(EuclideanSpace ℝ (Fin d), ℝ)) :
    normeK K n g ≤ (Finset.range (n + 1)).sup
      (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g :=
  normeK_le (apply_nonneg _ _) fun _ _ j hj w =>
    (norm_derivPartielle_le j w g _).trans
      ((ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))

/-- Pour `g ∈ 𝓓_K` et `i ≤ n`, la `i`-ème semi-norme de Mathlib est majorée par
`(d+1)^n` fois la semi-norme du cours. -/
lemma seminorm_le_normeK {i n : ℕ} (hi : i ≤ n) (g : 𝓓_{K}(EuclideanSpace ℝ (Fin d), ℝ)) :
    ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K i g ≤
      ((d : ℝ) + 1) ^ n * normeK K n g := by
  have hN := normeK_nonneg (K : Set (EuclideanSpace ℝ (Fin d))) n g
  have hbound : ∀ x ∈ (K : Set (EuclideanSpace ℝ (Fin d))), ∀ j ≤ n, ∀ w : Fin j → Fin d,
      ‖derivPartielle j w g x‖ ≤ (Finset.range (n + 1)).sup
        (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g :=
    fun _ _ j hj w => (norm_derivPartielle_le j w g _).trans
      ((ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hj))))
  rw [ContDiffMapSupportedIn.seminorm_top_le_iff ℝ (by positivity)]
  intro x hx
  calc ‖iteratedFDeriv ℝ i g x‖ ≤ ∑ w : Fin i → Fin d, ‖derivPartielle i w g x‖ :=
        norm_iteratedFDeriv_le_sum i g x
    _ ≤ ∑ _w : Fin i → Fin d, normeK K n g :=
        Finset.sum_le_sum fun w _ => le_normeK hbound hx hi w
    _ = (d : ℝ) ^ i * normeK K n g := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring
    _ ≤ ((d : ℝ) + 1) ^ n * normeK K n g := by
        gcongr
        calc (d : ℝ) ^ i ≤ ((d : ℝ) + 1) ^ i := pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) i
          _ ≤ ((d : ℝ) + 1) ^ n := pow_le_pow_right₀ (by linarith) hi

/-- **Déf. `def:cinf_bornee`, partie `𝓓_K(Ω)`.** Pour un compact `K`, l'espace `𝓓_K` des
fonctions `C^∞` à support dans `K` est l'espace Mathlib `𝓓_{K}(ℝ^d, ℝ)`
(`ContDiffMapSupportedIn`). Les semi-normes du cours `|f|_n = max_{|α|_1 ≤ n} ‖∂_α f‖_∞`
(ici `normeK K n`, le sup sur `K` coïncidant avec le sup sur `ℝ^d` puisque `f = 0` hors de `K`)
et le max `S_n` des semi-normes de Mathlib `sup_x ‖D^i f(x)‖`, `i ≤ n`, sont équivalentes :
`|f|_n ≤ S_n(f) ≤ (d+1)^n |f|_n`. Elles définissent donc la même topologie.
Remarque : l'espace `C^∞_b(Ω)` lui-même n'existe pas dans Mathlib et n'est pas formalisé. -/
theorem def_cinf_bornee_DK (n : ℕ) (g : 𝓓_{K}(EuclideanSpace ℝ (Fin d), ℝ)) :
    normeK K n g ≤ (Finset.range (n + 1)).sup
        (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g ∧
      (Finset.range (n + 1)).sup
        (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g ≤
        ((d : ℝ) + 1) ^ n * normeK K n g :=
  ⟨normeK_le_sup_seminorm n g, Seminorm.finset_sup_apply_le
    (mul_nonneg (by positivity) (normeK_nonneg _ _ _)) fun _ hi =>
      seminorm_le_normeK (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) g⟩

/-- Critère de continuité sur `𝓓_K` : une forme linéaire `ψ` sur `𝓓_K` est continue si et
seulement si elle vérifie une estimation `|ψ(g)| ≤ C max_{|α|_1 ≤ n} ‖∂_α g‖_{L^∞(K)}`. -/
lemma continuous_iff_normeK (ψ : 𝓓_{K}(EuclideanSpace ℝ (Fin d), ℝ) →ₗ[ℝ] ℝ) :
    Continuous ψ ↔ ∃ C : ℝ, ∃ n : ℕ, ∀ g, |ψ g| ≤ C * normeK K n g := by
  have hp := ContDiffMapSupportedIn.withSeminorms ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K
  constructor
  · intro hψ
    obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous hp ((normSeminorm ℝ ℝ).comp ψ)
      (continuous_norm.comp hψ)
    refine ⟨C * ((d : ℝ) + 1) ^ (s.sup id), s.sup id, fun g => ?_⟩
    calc |ψ g| = ((normSeminorm ℝ ℝ).comp ψ) g := rfl
      _ ≤ (C • s.sup (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K)) g :=
          hC g
      _ = C * s.sup (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g :=
          rfl
      _ ≤ C * (((d : ℝ) + 1) ^ (s.sup id) * normeK K (s.sup id) g) := by
          gcongr
          exact Seminorm.finset_sup_apply_le
            (mul_nonneg (by positivity) (normeK_nonneg _ _ _)) fun i hi =>
            seminorm_le_normeK (Finset.le_sup (f := id) hi) g
      _ = C * ((d : ℝ) + 1) ^ (s.sup id) * normeK K (s.sup id) g := by ring
  · rintro ⟨C, n, hC⟩
    refine hp.continuous_normedSpace_rng ℝ ψ ⟨Finset.range (n + 1), C.toNNReal, fun g => ?_⟩
    calc ‖ψ g‖ = |ψ g| := rfl
      _ ≤ C * normeK K n g := hC g
      _ ≤ C.toNNReal * normeK K n g := by
          gcongr
          · exact normeK_nonneg _ _ _
          · exact Real.le_coe_toNNReal C
      _ ≤ C.toNNReal * (Finset.range (n + 1)).sup
          (ContDiffMapSupportedIn.seminorm ℝ (EuclideanSpace ℝ (Fin d)) ℝ ⊤ K) g := by
          gcongr
          exact normeK_le_sup_seminorm n g

/-- **Déf. `def:distribution` (Fonctions test `𝓓(Ω)` et distributions).** Les fonctions test
`𝓓(Ω) = C^∞_c(Ω)` sont l'espace Mathlib `𝓓(Ω, ℝ)` (`TestFunction`), muni de sa topologie
limite inductive canonique, et les distributions de Mathlib (`𝓓'(Ω, ℝ)`) sont les formes
linéaires continues sur `𝓓(Ω, ℝ)`. Une forme linéaire `φ` sur `𝓓(Ω)` est continue si et
seulement si elle vérifie l'estimation locale du cours `eq:distrib_cont_loc` :
`∀ K ⊂⊂ Ω, ∃ C_K, ∃ n_K, ∀ f ∈ 𝓓_K(Ω), |φ(f)| ≤ C_K max_{|α|_1 ≤ n_K} ‖∂_α f‖_{L^∞(K)}`.
Remarques : les fonctions test de Mathlib sont définies sur `ℝ^d` entier, nulles hors d'un
compact de `Ω` (identification standard avec les fonctions sur `Ω`) ; `𝓓_K(Ω)` est décrit par
la condition `tsupport f ⊆ K` ; dérivées partielles indexées par des mots (cf.
`derivPartielle`). -/
theorem def_distribution (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    (φ : 𝓓(Ω, ℝ) →ₗ[ℝ] ℝ) :
    Continuous φ ↔ ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → K ⊆ Ω →
      ∃ C : ℝ, ∃ n : ℕ, ∀ f : 𝓓(Ω, ℝ), tsupport f ⊆ K → |φ f| ≤ C * normeK K n f := by
  rw [TestFunction.continuous_iff_continuous_comp (𝕜 := ℝ)]
  constructor
  · intro h K hK hKΩ
    let K' : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin d)) := ⟨K, hK⟩
    obtain ⟨C, n, hC⟩ := (continuous_iff_normeK (K := K')
      (φ.comp (TestFunction.ofSupportedInCLM ℝ (K := K') hKΩ).toLinearMap)).1 (h K' hKΩ)
    refine ⟨C, n, fun f hf => ?_⟩
    let g : 𝓓_{K'}(EuclideanSpace ℝ (Fin d), ℝ) :=
      ⟨f, f.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hf h)⟩
    have hfg : TestFunction.ofSupportedIn hKΩ g = f := TestFunction.ext fun _ => rfl
    have := hC g
    rwa [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, TestFunction.coe_ofSupportedInCLM,
      hfg] at this
  · intro h K hKΩ
    obtain ⟨C, n, hC⟩ := h K K.isCompact hKΩ
    exact (continuous_iff_normeK
      (φ.comp (TestFunction.ofSupportedInCLM ℝ (K := K) hKΩ).toLinearMap)).2
      ⟨C, n, fun g => hC _ g.tsupport_subset⟩

end Distribution

/-! ### Le lemme `lem:omegaNmuN` -/

/-- **Lemme `lem:omegaNmuN`.** Si `ω_n ≥ 0` (noté `w n`), `μ_n > 0` et `∑ μ_n = 1`, alors
`∑ ω_n ≤ sup_n ω_n / μ_n` (énoncé dans `[0, ∞]`, où somme et supremum ont toujours un sens). -/
theorem lem_omegaNmuN (w μ : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hμ : ∀ n, 0 < μ n)
    (hsum : HasSum μ 1) :
    ∑' n, ENNReal.ofReal (w n) ≤ ⨆ n, ENNReal.ofReal (w n / μ n) := by
  set S := ⨆ n, ENNReal.ofReal (w n / μ n)
  calc ∑' n, ENNReal.ofReal (w n) = ∑' n, ENNReal.ofReal (w n / μ n) * ENNReal.ofReal (μ n) := by
        congr 1; ext n
        rw [← ENNReal.ofReal_mul (div_nonneg (hw n) (hμ n).le), div_mul_cancel₀ _ (hμ n).ne']
    _ ≤ ∑' n, S * ENNReal.ofReal (μ n) :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr; exact le_iSup (fun n => ENNReal.ofReal (w n / μ n)) n
    _ = S := by
        rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (hμ n).le)
          hsum.summable, hsum.tsum_eq, ENNReal.ofReal_one, mul_one]

/-- **Lemme `lem:omegaNmuN`, version réelle.** Si de plus `ω_n / μ_n ≤ M` pour tout `n`, alors
la série `∑ ω_n` converge et `∑ ω_n ≤ M`. -/
theorem lem_omegaNmuN_reel (w μ : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hμ : ∀ n, 0 < μ n)
    (hsum : HasSum μ 1) (M : ℝ) (hM : ∀ n, w n / μ n ≤ M) :
    Summable w ∧ ∑' n, w n ≤ M := by
  have hle : ∀ n, w n ≤ M * μ n := fun n => by
    have := hM n
    rwa [div_le_iff₀ (hμ n)] at this
  have hs : Summable w := Summable.of_nonneg_of_le hw hle (hsum.summable.mul_left M)
  refine ⟨hs, ?_⟩
  calc ∑' n, w n ≤ ∑' n, M * μ n := hs.tsum_le_tsum hle (hsum.summable.mul_left M)
    _ = M := by rw [tsum_mul_left, hsum.tsum_eq, mul_one]

end M1Analyse
