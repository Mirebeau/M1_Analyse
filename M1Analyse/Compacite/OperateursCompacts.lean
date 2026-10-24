/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
# §3.8 Opérateurs linéaires compacts (`subsec:linCompact`)

Source : `Include/Compacite.tex`, sous-section `subsec:linCompact`.

Le corps `𝕂` du cours (`ℝ` ou `ℂ`) est un `RCLike 𝕜`. L'espace `L(E, F)` est `E →L[𝕜] F`,
un opérateur compact est un `IsCompactOperator T` de Mathlib, et `L_c(E, F)` est le
sous-module `compactOperator (RingHom.id 𝕜) E F`. Le spectre `σ(T)` est `spectrum 𝕜 T`
(dans l'algèbre `E →L[𝕜] E`), et les valeurs propres sont données par
`Module.End.HasEigenvalue`. Le théorème de Fredholm est
`IsCompactOperator.hasEigenvalue_or_mem_resolventSet` de Mathlib.

Non formalisés : l'exemple d'opérateur intégral `lem:convK_compact` et son
application `corol:eqFuncNoyau`.
-/

open Set Metric Filter Topology

namespace M1Analyse

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- **Déf. `def:linCompact` (Opérateur linéaire compact).** Un opérateur `T ∈ L(E, F)` est
compact si `T(B_E(0,1))` est relativement compact, i.e. `\overline{T(B_E(0,1))}` est compact. -/
theorem def_linCompact (T : E →L[𝕜] F) :
    IsCompactOperator T ↔ IsCompact (closure (T '' ball 0 1)) :=
  isCompactOperator_iff_isCompact_closure_image_ball (T : E →ₗ[𝕜] F) zero_lt_one

/-- **Déf. `def:linCompact`, notation `L_c(E, F)`.** L'ensemble `L_c(E, F)` des opérateurs
compacts est (le sous-module Mathlib) `compactOperator`. -/
theorem def_linCompact_Lc :
    (compactOperator (RingHom.id 𝕜) E F : Set (E →L[𝕜] F)) =
      {T : E →L[𝕜] F | IsCompact (closure (T '' ball 0 1))} := by
  ext T
  exact def_linCompact T

/-- **Prop. `prop:opCompactComposition` (Composition), à gauche.** Si `T ∈ L_c(E, F)` et
`A ∈ L(F, G)`, alors `A ∘ T` est compact. -/
theorem prop_opCompactComposition_left (T : E →L[𝕜] F) (A : F →L[𝕜] G)
    (hT : IsCompactOperator T) : IsCompactOperator (A ∘L T) :=
  hT.clm_comp A

/-- **Prop. `prop:opCompactComposition` (Composition), à droite.** Si `A ∈ L(E, F)` et
`T ∈ L_c(F, G)`, alors `T ∘ A` est compact. -/
theorem prop_opCompactComposition_right (A : E →L[𝕜] F) (T : F →L[𝕜] G)
    (hT : IsCompactOperator T) : IsCompactOperator (T ∘L A) :=
  hT.comp_clm A

/-- **Prop. `prop:opCompactLimite`, premier point.** Si `F` est un Banach, l'ensemble
`L_c(E, F)` est fermé dans `L(E, F)`. -/
theorem prop_opCompactLimite_isClosed [CompleteSpace F] :
    IsClosed {T : E →L[𝕜] F | IsCompactOperator T} :=
  isClosed_setOfPred_isCompactOperator

/-- **Déf. `def:linSpectre` (Spectre).** `λ ∈ σ(T)` si et seulement si `λ Id - T` n'a pas
d'inverse continu. -/
theorem def_linSpectre [CompleteSpace E] (T : E →L[𝕜] E) (μ : 𝕜) :
    μ ∈ spectrum 𝕜 T ↔
      ¬ ∃ S : E →L[𝕜] E, S ∘L (μ • ContinuousLinearMap.id 𝕜 E - T) = ContinuousLinearMap.id 𝕜 E ∧
        (μ • ContinuousLinearMap.id 𝕜 E - T) ∘L S = ContinuousLinearMap.id 𝕜 E := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, isUnit_iff_exists]
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def]
  constructor <;> rintro h ⟨S, h1, h2⟩ <;> exact h ⟨S, h2, h1⟩

/-- **Déf. `def:linSpectre` (Valeur propre).** `λ` est valeur propre de `T` (au sens de
`Module.End.HasEigenvalue`) si et seulement si c'est une valeur spectrale dont l'espace propre
`E_λ := Ker(λ Id - T)` n'est pas réduit à `{0}`. -/
theorem def_linSpectre_valeurPropre [CompleteSpace E] (T : E →L[𝕜] E) (μ : 𝕜) :
    Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) μ ↔
      μ ∈ spectrum 𝕜 T ∧ LinearMap.ker ((μ • ContinuousLinearMap.id 𝕜 E - T : E →L[𝕜] E) :
        E →ₗ[𝕜] E) ≠ ⊥ := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    have hTx : T x = μ • x := Module.End.mem_eigenspace_iff.1 hx.1
    have hker : (μ • ContinuousLinearMap.id 𝕜 E - T) x = 0 := by simp [hTx]
    refine ⟨(def_linSpectre T μ).2 ?_, (Submodule.ne_bot_iff _).2 ⟨x, hker, hx.2⟩⟩
    rintro ⟨S, h1, -⟩
    apply hx.2
    have := congrArg (fun L : E →L[𝕜] E => L x) h1
    simp only [ContinuousLinearMap.comp_apply, hker, map_zero,
      ContinuousLinearMap.id_apply] at this
    exact this.symm
  · rintro ⟨-, hk⟩
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hk
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ⟨?_, hx0⟩
    rw [Module.End.mem_eigenspace_iff]
    have : μ • x - T x = 0 := by simpa using hx
    exact (sub_eq_zero.1 this).symm

/-- **Thm. `th:Fredholm` (Fredholm).** Soit `E` un Banach et `T ∈ L_c(E)` un opérateur compact
tel que `Ker(Id - T) = {0}`. Alors `Im(Id - T) = E`, et `Id - T` admet un inverse continu.
Preuve (différente du cours) : alternative de Fredholm de Mathlib
(`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) ; ni fermeture de `Im(Id - T)`, ni
suite décroissante `(Id - T)^n E` avec le lemme de Riesz, ni isomorphisme de Banach. -/
theorem th_Fredholm [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hker : LinearMap.ker ((ContinuousLinearMap.id 𝕜 E - T : E →L[𝕜] E) : E →ₗ[𝕜] E) = ⊥) :
    LinearMap.range ((ContinuousLinearMap.id 𝕜 E - T : E →L[𝕜] E) : E →ₗ[𝕜] E) = ⊤ ∧
      ∃ S : E →L[𝕜] E, S ∘L (ContinuousLinearMap.id 𝕜 E - T) = ContinuousLinearMap.id 𝕜 E ∧
        (ContinuousLinearMap.id 𝕜 E - T) ∘L S = ContinuousLinearMap.id 𝕜 E := by
  have h1 : ¬ Module.End.HasEigenvalue (T : E →ₗ[𝕜] E) 1 := by
    rw [def_linSpectre_valeurPropre]
    rintro ⟨-, h⟩
    exact h (by simpa only [one_smul] using hker)
  have hres := (hT.hasEigenvalue_or_mem_resolventSet one_ne_zero).resolve_left h1
  have hσ : (1 : 𝕜) ∉ spectrum 𝕜 T := fun h => h hres
  rw [def_linSpectre, not_not] at hσ
  obtain ⟨S, hS1, hS2⟩ := hσ
  simp only [one_smul] at hS1 hS2
  refine ⟨LinearMap.range_eq_top.2 fun y => ⟨S y, ?_⟩, S, hS1, hS2⟩
  exact congrArg (fun L : E →L[𝕜] E => L y) hS2

/-- **Cor. `corol:FredholmPrecise` (Fredholm précisé), point (i).** Soit `E` un Banach et
`T ∈ L_c(E)`. Si `dim(E) = ∞` alors `0 ∈ σ(T)`. -/
theorem corol_FredholmPrecise_i [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (hdim : ¬ FiniteDimensional 𝕜 E) : (0 : 𝕜) ∈ spectrum 𝕜 T := by
  by_contra h
  rw [def_linSpectre, not_not] at h
  obtain ⟨S, hS, -⟩ := h
  apply hdim
  apply FiniteDimensional.of_isCompactOperator_id
  have hc := hT.clm_comp (-S)
  have : (⇑(-S) ∘ ⇑T : E → E) = id := by
    funext x
    have := congrArg (fun L : E →L[𝕜] E => L x) hS
    simpa using this
  rwa [this] at hc

/-- **Cor. `corol:FredholmPrecise` (Fredholm précisé), point (ii).** Soit `E` un Banach et
`T ∈ L_c(E)`. Pour tout `λ ∈ σ(T) ∖ {0}`, il existe `x ∈ E ∖ {0}` tel que `T x = λ x`
(`λ` est valeur propre). -/
theorem corol_FredholmPrecise_ii [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (μ : 𝕜) (hμ : μ ∈ spectrum 𝕜 T \ {0}) : ∃ x : E, x ≠ 0 ∧ T x = μ • x := by
  obtain ⟨x, hx⟩ := ((hT.hasEigenvalue_iff_mem_spectrum hμ.2).2 hμ.1).exists_hasEigenvector
  exact ⟨x, hx.2, Module.End.mem_eigenspace_iff.1 hx.1⟩

/-- Dans un espace séparé, un point d'adhérence d'une suite convergente est sa limite. -/
private lemma eq_of_mapClusterPt_of_tendsto {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    {u : ℕ → Y} {a b : Y} (ha : MapClusterPt a atTop u) (hb : Tendsto u atTop (𝓝 b)) :
    a = b := by
  by_contra hne
  have h1 : ClusterPt a (𝓝 b) := ClusterPt.mono ha hb
  exact h1.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))

/-- **Prop. `prop:opCompactComplCont` (Complète continuité des opérateurs compacts), premier
point.** Soit `T ∈ L_c(E, F)` et `x_n ⇀ x_*` une suite de `E` convergeant faiblement (i.e. pour
la topologie faible `WeakSpace 𝕜 E`). Alors `T x_n → T x_*` en norme.
Le second point est `prop_opCompactComplCont_boule`. -/
theorem prop_opCompactComplCont (T : E →L[𝕜] F) (hT : IsCompactOperator T) (x : ℕ → E)
    (x₀ : E) (hx : Tendsto (fun n => toWeakSpace 𝕜 E (x n)) atTop (𝓝 (toWeakSpace 𝕜 E x₀))) :
    Tendsto (fun n => T (x n)) atTop (𝓝 (T x₀)) := by
  -- convergence faible : `φ (x n) → φ x₀` pour toute forme linéaire continue `φ`
  have hφ : ∀ φ : StrongDual 𝕜 E, Tendsto (fun n => φ (x n)) atTop (𝓝 (φ x₀)) := fun φ =>
    ((WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip φ).tendsto _).comp hx
  -- la suite est bornée (Banach-Steinhaus dans le bidual)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun n => NormedSpace.inclusionInDoubleDual 𝕜 E (x n))
    (fun φ => by
      obtain ⟨C, hC⟩ := (hφ φ).norm.bddAbove_range
      exact ⟨C, fun n => hC ⟨n, rfl⟩⟩)
  have hxC : ∀ n, x n ∈ closedBall (0 : E) C := fun n => by
    rw [mem_closedBall_zero_iff]
    have := (NormedSpace.inclusionInDoubleDualLi 𝕜 (E := E)).norm_map (x n)
    exact this ▸ hC n
  -- les `T x_n` restent dans le compact `\overline{T(B'(0, C))}`, et y ont `T x₀` pour unique
  -- valeur d'adhérence
  refine (hT.isCompact_closure_image_closedBall C).tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure (mem_image_of_mem _ (hxC n))) ?_
  intro y _ hy
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)]
  intro φ
  have h1 : MapClusterPt (φ y) atTop (fun n => φ (T (x n))) :=
    hy.continuousAt_comp φ.continuous.continuousAt
  exact eq_of_mapClusterPt_of_tendsto h1 (hφ (φ ∘L T))

/-- Argument de Riesz commun aux points (iii) et (iv) du `corol:FredholmPrecise` : pour `T`
compact, il n'existe pas de suite strictement croissante de sous-espaces fermés `V n`, stables
par `T`, avec `(μ_n Id - T)(V_{n+1}) ⊆ V_n` et `‖μ_n‖ ≥ ε > 0`. -/
private lemma riesz_seq_false (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (V : ℕ → Submodule 𝕜 E) (hVc : ∀ n, IsClosed (V n : Set E)) (hVlt : ∀ n, V n < V (n + 1))
    (μ : ℕ → 𝕜) (ε : ℝ) (hε : 0 < ε) (hμ : ∀ n, ε ≤ ‖μ n‖)
    (hTV : ∀ n, ∀ x ∈ V n, T x ∈ V n) (hμV : ∀ n, ∀ x ∈ V (n + 1), μ n • x - T x ∈ V n) :
    False := by
  have hmono : Monotone V := monotone_nat_of_le_succ fun n => (hVlt n).le
  -- lemme de Riesz dans `V (n+1)`, relativement au sous-espace fermé `V n`
  have hR : ∀ n, ∃ x ∈ V (n + 1), ‖x‖ ≤ 3 ∧ ∀ y ∈ V n, 1 ≤ ‖x - y‖ := by
    intro n
    set W := V (n + 1)
    set F' : Submodule 𝕜 W := (V n).comap W.subtype
    have hF'c : IsClosed (F' : Set W) := (hVc n).preimage continuous_subtype_val
    have hF' : ∃ x : W, x ∉ F' := by
      obtain ⟨x, hxW, hxn⟩ := SetLike.exists_of_lt (hVlt n)
      exact ⟨⟨x, hxW⟩, hxn⟩
    have h2 : ‖(2 : 𝕜)‖ = 2 := by simp
    obtain ⟨x, hx, hxy⟩ := riesz_lemma_of_norm_lt (c := (2 : 𝕜)) (by rw [h2]; norm_num)
      (R := 3) (by rw [h2]; norm_num) hF'c hF'
    refine ⟨x, x.2, hx, fun y hy => ?_⟩
    have := hxy ⟨y, (hVlt n).le hy⟩ hy
    exact this
  choose x hxV hxn hxsep using hR
  -- les `T x_n` sont `ε`-séparés
  have hsep : ∀ m n, m < n → ε ≤ ‖T (x n) - T (x m)‖ := by
    intro m n hmn
    have hμ0 : μ n ≠ 0 := fun h => by
      have := hμ n; rw [h, norm_zero] at this; linarith
    set z := (μ n • x n - T (x n)) + T (x m)
    have hz : z ∈ V n := (V n).add_mem (hμV n _ (hxV n))
      (hmono (Nat.succ_le_of_lt hmn) (hTV _ _ (hxV m)))
    have heq : T (x n) - T (x m) = μ n • (x n - (μ n)⁻¹ • z) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      simp only [z]
      abel
    rw [heq, norm_smul]
    calc ε = ε * 1 := (mul_one ε).symm
      _ ≤ ‖μ n‖ * ‖x n - (μ n)⁻¹ • z‖ :=
        mul_le_mul (hμ n) (hxsep n _ ((V n).smul_mem _ hz)) zero_le_one (norm_nonneg _)
  -- contradiction avec la compacité
  obtain ⟨a, -, φ, hφ, hlim⟩ := (hT.isCompact_closure_image_closedBall 3).tendsto_subseq
    (x := fun n => T (x n))
    (fun n => subset_closure (mem_image_of_mem _ (mem_closedBall_zero_iff.2 (hxn n))))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  have h3 := hsep (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
  have : dist (T (x (φ (N + 1)))) (T (x (φ N))) < ε := by
    calc _ ≤ dist (T (x (φ (N + 1)))) a + dist a (T (x (φ N))) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add h2 (by rw [dist_comm]; exact h1)
      _ = ε := add_halves ε
  rw [dist_eq_norm] at this
  linarith

/-- **Prop. `prop:opCompactComplCont` (Complète continuité des opérateurs compacts), second
point.** Soit `T ∈ L_c(E, F)`. Alors la restriction `T : B'_E(0,1) → F` est continue de la
topologie faible (`WeakSpace 𝕜 E`) dans la topologie forte (de la norme de `F`).
Remarque : le cours suppose `E*` séparable, ce qui rend la topologie faible métrisable sur la
boule et permet de raisonner par suites. Cette hypothèse est superflue : l'argument de
compacité du premier point s'applique directement aux filtres (suites généralisées). -/
theorem prop_opCompactComplCont_boule
    (T : E →L[𝕜] F) (hT : IsCompactOperator T) :
    ContinuousOn (fun w : WeakSpace 𝕜 E => T ((toWeakSpace 𝕜 E).symm w))
      (toWeakSpace 𝕜 E '' closedBall 0 1) := by
  intro w _
  set f : WeakSpace 𝕜 E → F := fun w => T ((toWeakSpace 𝕜 E).symm w) with hf
  -- pour toute forme `φ ∈ F*`, `φ ∘ T` est faiblement continue
  have hφ : ∀ φ : StrongDual 𝕜 F,
      Tendsto (fun v => φ (f v)) (𝓝[toWeakSpace 𝕜 E '' closedBall 0 1] w) (𝓝 (φ (f w))) :=
    fun φ => ((WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip (φ ∘L T)).tendsto w).mono_left
      nhdsWithin_le_nhds
  refine (hT.isCompact_closure_image_closedBall 1).tendsto_nhds_of_unique_mapClusterPt
    (eventually_nhdsWithin_of_forall fun v hv => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := hv
    exact subset_closure (mem_image_of_mem _ (by simpa using hx))
  intro y _ hy
  rw [SeparatingDual.eq_iff_forall_dual_eq (R := 𝕜)]
  intro φ
  have h1 : MapClusterPt (φ y) (𝓝[toWeakSpace 𝕜 E '' closedBall 0 1] w) (fun v => φ (f v)) :=
    hy.continuousAt_comp φ.continuous.continuousAt
  by_contra hne
  have h2 : ClusterPt (φ y) (𝓝 (φ (f w))) := ClusterPt.mono h1 (hφ φ)
  exact h2.ne (disjoint_iff.1 (disjoint_nhds_nhds.2 hne))

/-- **Cor. `corol:FredholmPrecise` (Fredholm précisé), point (iii).** Soit `E` un Banach et
`T ∈ L_c(E)`. Pour tout `λ ∈ σ(T) ∖ {0}`, il existe `m` tel que
`Ker((λ Id - T)^m) = Ker((λ Id - T)^{m+1})`, et de plus `dim Ker((λ Id - T)^m) < ∞`. -/
theorem corol_FredholmPrecise_iii [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (μ : 𝕜) (hμ : μ ∈ spectrum 𝕜 T \ {0}) :
    ∃ m : ℕ, LinearMap.ker (((μ • ContinuousLinearMap.id 𝕜 E - T) ^ m : E →L[𝕜] E) :
        E →ₗ[𝕜] E) =
      LinearMap.ker (((μ • ContinuousLinearMap.id 𝕜 E - T) ^ (m + 1) : E →L[𝕜] E) :
        E →ₗ[𝕜] E) ∧
      FiniteDimensional 𝕜 (LinearMap.ker (((μ • ContinuousLinearMap.id 𝕜 E - T) ^ m :
        E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
  set A : E →L[𝕜] E := μ • ContinuousLinearMap.id 𝕜 E - T with hA
  have hμ0 : μ ≠ 0 := hμ.2
  have hcomm : Commute T A :=
    ((Commute.one_right T).smul_right μ).sub_right (Commute.refl T)
  -- stabilisation des noyaux itérés, par l'argument de Riesz
  have hstab : ∃ m, LinearMap.ker ((A ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E) =
      LinearMap.ker ((A ^ (m + 1) : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    by_contra! h
    refine riesz_seq_false T hT (fun n => LinearMap.ker ((A ^ n : E →L[𝕜] E) : E →ₗ[𝕜] E))
      (fun n => ContinuousLinearMap.isClosed_ker (A ^ n)) (fun n => lt_of_le_of_ne ?_ (h n))
      (fun _ => μ) ‖μ‖ (norm_pos_iff.2 hμ0) (fun _ => le_rfl) ?_ ?_
    · intro x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      rw [pow_succ', mul_apply_eq_comp, hx, map_zero]
    · intro n x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      rw [← mul_apply_eq_comp, ← (hcomm.pow_right n).eq,
        mul_apply_eq_comp, hx, map_zero]
    · intro n x hx
      simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
      have : μ • x - T x = A x := by simp [hA]
      rw [this, ← mul_apply_eq_comp, ← pow_succ, hx]
  obtain ⟨m, hm⟩ := hstab
  refine ⟨m, hm, ?_⟩
  -- dimension finie : `μ^m Id - A^m = B T` est compact et vaut `μ^m Id` sur `Ker(A^m)`
  set W := LinearMap.ker ((A ^ m : E →L[𝕜] E) : E →ₗ[𝕜] E)
  set B : E →L[𝕜] E :=
    ∑ i ∈ Finset.range m, (μ • (1 : E →L[𝕜] E)) ^ i * A ^ (m - 1 - i)
  have hBT : B * T = (μ • (1 : E →L[𝕜] E)) ^ m - A ^ m := by
    have h := ((Commute.one_left A).smul_left μ).geom_sum₂_mul m
    have hsub : μ • (1 : E →L[𝕜] E) - A = T := by
      simp only [hA, ContinuousLinearMap.one_def]; abel
    rwa [hsub] at h
  set S : E →L[𝕜] E := (μ ^ m)⁻¹ • (B * T)
  have hS : IsCompactOperator S := (hT.clm_comp B).smul _
  have hSW : ∀ v ∈ W, S v = v := by
    intro v hv
    have hv' : (A ^ m) v = 0 := hv
    simp only [S, hBT, smul_apply, sub_apply, hv', sub_zero, smul_pow, one_pow,
      one_apply_eq_self, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hμ0), one_smul]
  have hV : ∀ v ∈ W, (S : E →ₗ[𝕜] E) v ∈ W := fun v hv => by
    simpa [hSW v hv] using hv
  have : CompleteSpace W := (ContinuousLinearMap.isClosed_ker (A ^ m)).completeSpace_coe
  have hc := (hS : IsCompactOperator (S : E →ₗ[𝕜] E)).restrict' hV
  have hid : ((S : E →ₗ[𝕜] E).restrict hV : W → W) = id := by
    funext v
    exact Subtype.ext (hSW v v.2)
  rw [hid] at hc
  exact FiniteDimensional.of_isCompactOperator_id hc

/-- Étape de la preuve du point (iv) du `corol:FredholmPrecise` : pour tout `ε > 0`, il n'y a
qu'un nombre fini de valeurs spectrales de module `≥ ε`. -/
private lemma finite_spectrum_ge [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T)
    (ε : ℝ) (hε : 0 < ε) : {μ ∈ spectrum 𝕜 T | ε ≤ ‖μ‖}.Finite := by
  by_contra hinf
  set e := Set.Infinite.natEmbedding _ hinf
  set ν : ℕ → 𝕜 := fun n => (e n : 𝕜)
  have hνinj : Function.Injective ν := fun a b h => e.injective (Subtype.ext h)
  have hνσ : ∀ n, ν n ∈ spectrum 𝕜 T := fun n => (e n).2.1
  have hνε : ∀ n, ε ≤ ‖ν n‖ := fun n => (e n).2.2
  have hν0 : ∀ n, ν n ≠ 0 := fun n h => by
    have := hνε n; rw [h, norm_zero] at this; linarith
  choose v hv0 hTv using fun n => corol_FredholmPrecise_ii T hT (ν n) ⟨hνσ n, hν0 n⟩
  have hli : LinearIndependent 𝕜 v :=
    Module.End.eigenvectors_linearIndependent' (T : E →ₗ[𝕜] E) ν hνinj v
      fun i => ⟨Module.End.mem_eigenspace_iff.2 (hTv i), hv0 i⟩
  set V : ℕ → Submodule 𝕜 E := fun n => Submodule.span 𝕜 (v '' {i | i < n})
  have hVfin : ∀ n, FiniteDimensional 𝕜 (V n) := fun n =>
    FiniteDimensional.span_of_finite 𝕜 ((Set.finite_lt_nat n).image v)
  refine riesz_seq_false T hT V (fun n => Submodule.closed_of_finiteDimensional _)
    (fun n => ?_) ν ε hε hνε (fun n => ?_) (fun n => ?_)
  · refine SetLike.lt_iff_le_and_exists.2 ⟨Submodule.span_mono (image_mono fun i hi => ?_),
      v n, Submodule.subset_span ⟨n, Nat.lt_succ_self n, rfl⟩, ?_⟩
    · exact Nat.lt_succ_of_lt hi
    · exact hli.notMem_span_image (fun h => lt_irrefl n h)
  · intro x hx
    have : V n ≤ (V n).comap (T : E →ₗ[𝕜] E) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe, hTv i]
      exact (V n).smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    exact this hx
  · intro x hx
    have : V (n + 1) ≤ (V n).comap ((ν n • ContinuousLinearMap.id 𝕜 E - T : E →L[𝕜] E) :
        E →ₗ[𝕜] E) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
      simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply, hTv i, ← sub_smul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact (V n).smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
      · simp
    have := this hx
    simpa using this

/-- **Cor. `corol:FredholmPrecise` (Fredholm précisé), point (iv).** Soit `E` un Banach et
`T ∈ L_c(E)`. L'ensemble `σ(T) ⊆ B'(0, ‖T‖)` est dénombrable, et `0` est son seul point
d'accumulation possible.
Preuve (ordre différent du cours) : on montre d'abord que `σ(T) ∩ {|λ| ≥ ε}` est fini
(argument de Riesz sur les vecteurs propres), d'où dénombrabilité et point d'accumulation ;
la borne `|λ| ≤ ‖T‖` est `spectrum.subset_closedBall_norm` de Mathlib. -/
theorem corol_FredholmPrecise_iv [CompleteSpace E] (T : E →L[𝕜] E) (hT : IsCompactOperator T) :
    spectrum 𝕜 T ⊆ closedBall 0 ‖T‖ ∧ (spectrum 𝕜 T).Countable ∧
      ∀ μ : 𝕜, AccPt μ (𝓟 (spectrum 𝕜 T)) → μ = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rcases subsingleton_or_nontrivial E with hE | hE
    · intro μ hμ
      exfalso
      rw [def_linSpectre] at hμ
      exact hμ ⟨0, by ext x; exact Subsingleton.elim _ _, by ext x; exact Subsingleton.elim _ _⟩
    · exact spectrum.subset_closedBall_norm T
  · have hsub : spectrum 𝕜 T ⊆ {0} ∪ ⋃ k : ℕ, {μ ∈ spectrum 𝕜 T | 1 / ((k : ℝ) + 1) ≤ ‖μ‖} := by
      intro μ hμ
      by_cases h0 : μ = 0
      · exact Or.inl h0
      · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.2 h0)
        exact Or.inr (mem_iUnion.2 ⟨k, hμ, hk.le⟩)
    refine Countable.mono hsub ((countable_singleton 0).union (countable_iUnion fun k => ?_))
    exact (finite_spectrum_ge T hT _ (by positivity)).countable
  · intro μ hμ
    by_contra h0
    set ε := ‖μ‖ / 2 with hεdef
    have hε : 0 < ε := by positivity
    set S := {ν ∈ spectrum 𝕜 T | ε ≤ ‖ν‖} \ {μ}
    have hS : IsClosed S := ((finite_spectrum_ge T hT ε hε).sdiff).isClosed
    have hU : ball μ ε ∩ Sᶜ ∈ 𝓝 μ :=
      inter_mem (ball_mem_nhds μ hε) (hS.isOpen_compl.mem_nhds fun h => h.2 rfl)
    obtain ⟨y, ⟨⟨hyb, hyS⟩, hyσ⟩, hyμ⟩ := accPt_iff_nhds.1 hμ _ hU
    apply hyS
    refine ⟨⟨hyσ, ?_⟩, hyμ⟩
    rw [mem_ball, dist_eq_norm] at hyb
    have := norm_sub_norm_le μ y
    rw [norm_sub_rev] at this
    linarith

/-- **Prop. `prop:opCompactLimite`, second point.** Si `F` est un Hilbert, alors `L_c(E, F)` est
l'adhérence dans `L(E, F)` de l'ensemble des opérateurs de rang fini. -/
theorem prop_opCompactLimite_hilbert {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] :
    {T : E →L[𝕜] H | IsCompactOperator T} =
      closure {u : E →L[𝕜] H | FiniteDimensional 𝕜 (LinearMap.range (u : E →ₗ[𝕜] H))} := by
  apply Subset.antisymm
  · -- approximation par `P ∘ T`, `P` projection orthogonale sur un sous-espace de dimension finie
    intro T hT
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, -, htfin, hcov⟩ := finite_cover_balls_of_compact
      ((hT : IsCompactOperator T).isCompact_closure_image_closedBall 1) (e := ε / 3)
      (by positivity)
    set K := Submodule.span 𝕜 t
    have : FiniteDimensional 𝕜 K := FiniteDimensional.span_of_finite 𝕜 htfin
    set P := K.starProjection
    refine ⟨P ∘L T, ?_, ?_⟩
    · change FiniteDimensional 𝕜 (LinearMap.range ((P ∘L T : E →L[𝕜] H) : E →ₗ[𝕜] H))
      refine Submodule.finiteDimensional_of_le (S₂ := K) ?_
      rintro _ ⟨x, rfl⟩
      exact K.starProjection_apply_mem _
    · rw [dist_eq_norm]
      refine lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_of_unit_norm
        (C := 2 * (ε / 3)) (by positivity) fun x hx => ?_) (by linarith)
      have hTx : T x ∈ closure (T '' closedBall 0 1) :=
        subset_closure (mem_image_of_mem _ (mem_closedBall_zero_iff.2 hx.le))
      obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcov hTx)
      rw [mem_ball, dist_eq_norm] at hy
      have hPy : P y = y := (K.starProjection_eq_self_iff).2 (Submodule.subset_span hyt)
      have hP : ‖P (y - T x)‖ ≤ ‖y - T x‖ := K.norm_starProjection_apply_le _
      have : (T - P ∘L T) x = (T x - y) + P (y - T x) := by
        simp [map_sub, hPy]
      rw [this]
      calc ‖(T x - y) + P (y - T x)‖ ≤ ‖T x - y‖ + ‖P (y - T x)‖ := norm_add_le _ _
        _ ≤ ε / 3 + ε / 3 := by
          rw [norm_sub_rev] at hP
          linarith
        _ = 2 * (ε / 3) := by ring
  · -- un opérateur de rang fini est compact, et `L_c(E, F)` est fermé
    refine closure_minimal (fun u hu => ?_) prop_opCompactLimite_isClosed
    have : FiniteDimensional 𝕜 (LinearMap.range (u : E →ₗ[𝕜] H)) := hu
    set R := LinearMap.range (u : E →ₗ[𝕜] H)
    set u' : E →L[𝕜] R := u.codRestrict R (fun x => LinearMap.mem_range_self _ x)
    have h := (isCompactOperator_of_locallyCompactSpace_dom u').clm_comp R.subtypeL
    exact h

end M1Analyse
