/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact

/-!
# §2.4 Point fixe de Picard (`subsec:Picard`)

Source : `Include/Completude.tex`, sous-section `subsec:Picard`.

Le théorème du point fixe de Picard est `ContractingWith.fixedPoint` de Mathlib (avec
l'estimation a priori `ContractingWith.apriori_dist_iterate_fixedPoint_le`) ; le lemme de
Grönwall se déduit de `norm_le_gronwallBound_of_norm_deriv_right_le` ; le théorème de
Cauchy-Lipschitz (Picard-Lindelöf) s'obtient à partir de `IsPicardLindelof` et de
`dist_le_of_trajectories_ODE_of_mem`. `ℝ^d` est `EuclideanSpace ℝ (Fin d)`.
Les exemples `ex:EDretard` et `ex:eqFunctIntegr` sont démontrés comme dans le cours, par le
point fixe de Picard dans `C(Icc 0 (1/2), ℝ)` et `C(Icc 0 1, ℝ)` (norme uniforme).
Non formalisé : `corol:CauchyLipAuton` (la notion de solution maximale est absente de Mathlib).
-/

open Set Filter Topology Metric Function
open scoped NNReal

namespace M1Analyse

variable {X : Type*}

/-- **Th. `th:fixe_Picard` (Point fixe de Picard).** Soit `(X,d)` un espace métrique complet et
`f : X → X` `K`-lipschitzienne avec `K < 1`. Alors `f` admet un unique point fixe `x_*`, et pour
tout `x_0 ∈ X` et `n ∈ ℕ`, `d(x_n, x_*) ≤ K^n d(x_0, x_1)/(1 - K)` où `x_n := f^{∘n}(x_0)`.
Remarque : on suppose `X` non vide (hypothèse implicite dans le cours, nécessaire à
l'existence du point fixe). -/
theorem th_fixe_Picard [MetricSpace X] [CompleteSpace X] [Nonempty X] (K : ℝ≥0) (hK : K < 1)
    (f : X → X) (hf : LipschitzWith K f) :
    ∃ xs : X, (f xs = xs ∧ ∀ y, f y = y → y = xs) ∧
      ∀ (x₀ : X) (n : ℕ), dist (f^[n] x₀) xs ≤ (K : ℝ) ^ n * dist x₀ (f^[1] x₀) / (1 - K) := by
  have hc : ContractingWith K f := ⟨hK, hf⟩
  refine ⟨ContractingWith.fixedPoint f hc, ⟨hc.fixedPoint_isFixedPt,
    fun y hy => hc.fixedPoint_unique hy⟩, fun x₀ n => ?_⟩
  have := hc.apriori_dist_iterate_fixedPoint_le x₀ n
  rw [iterate_one, mul_comm ((K : ℝ) ^ n)]
  exact this

/-- **Lemme `lem:Gronwall` (Grönwall).** Soit `f ∈ C⁰([0,T], ℝ₊)` et `A, B ≥ 0` tels que
`f(t) ≤ A ∫_0^t f(s) ds + B` pour tout `t ∈ [0,T]`. Alors `f(t) ≤ B exp(A t)` pour tout
`t ∈ [0,T]`. -/
theorem lem_Gronwall (T A B : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ t ∈ Icc 0 T, f t ≤ A * (∫ s in (0)..t, f s) + B) :
    ∀ t ∈ Icc 0 T, f t ≤ B * Real.exp (A * t) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  set g : ℝ → ℝ := fun s => f (projIcc 0 T hT s) with hg_def
  have hg : Continuous g :=
    hf.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun s => (projIcc 0 T hT s).2)
  have hgf : ∀ s ∈ Icc 0 T, g s = f s := fun s hs => by simp [g, projIcc_of_mem hT hs]
  set F : ℝ → ℝ := fun s => A * (∫ r in (0)..s, g r) + B with hF_def
  have hFd : ∀ s, HasDerivAt F (A * g s) s := fun s =>
    ((hg.integral_hasStrictDerivAt 0 s).hasDerivAt.const_mul A).add_const B
  have hint : ∀ s ∈ Icc 0 T, ∫ r in (0)..s, g r = ∫ r in (0)..s, f r := fun s hs =>
    intervalIntegral.integral_congr fun r hr => hgf r (uIcc_subset_Icc ⟨le_rfl, hT⟩ hs hr)
  have hfF : ∀ s ∈ Icc 0 T, f s ≤ F s := fun s hs => by
    simp only [F, hint s hs]; exact h s hs
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := F) (f' := fun s => A * g s)
    (δ := B) (K := A) (ε := 0) (a := 0) (b := T)
    (fun s _ => (hFd s).continuousAt.continuousWithinAt) (fun s _ => (hFd s).hasDerivWithinAt)
    (by simp only [F, intervalIntegral.integral_same, mul_zero, zero_add, Real.norm_eq_abs,
      abs_of_nonneg hB, le_refl]) (fun s hs => by
      have hs' : s ∈ Icc 0 T := Ico_subset_Icc_self hs
      have h0 := hpos s hs'
      have h1 := hfF s hs'
      rw [hgf s hs', Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA h0),
        abs_of_nonneg (h0.trans h1), add_zero]
      exact mul_le_mul_of_nonneg_left h1 hA) t ht
  rw [gronwallBound_ε0, sub_zero] at key
  exact (hfF t ht).trans ((le_abs_self _).trans key)

/-- **Th. `th:Cauchy_Lipschitz` (Cauchy-Lipschitz, Picard-Lindelöf).** Soit `Ω ⊆ ℝ^d` ouvert et
`f : ℝ₊ × Ω → ℝ^d` continue et localement lipschitzienne en sa seconde variable
(`eq:loc_lip2`). Alors :
* (Existence) pour tout `x₀ ∈ Ω`, il existe `t₀ > 0` et une solution `u ∈ C¹([0,t₀], Ω)` de
  l'EDO `u'(t) = f(t, u(t))` (`eq:EDO`) avec `u(0) = x₀` ;
* (Stabilité) pour tous `T > 0` et `K ⊂ Ω` compact, il existe `C` tel que si `u, v` sont des
  solutions de `eq:EDO` sur `[0,T]` à valeurs dans `K`, alors
  `‖u(t) - v(t)‖ ≤ e^{Ct} ‖u(0) - v(0)‖` pour tout `t ∈ [0,T]`.

Remarques : `f` est une fonction `ℝ → ℝ^d → ℝ^d` dont seules les valeurs sur `ℝ₊ × Ω` comptent.
Une solution `C¹` sur `[0,t₀]` est une fonction `u` dérivable sur `[0,t₀]` (dérivées à droite
et à gauche aux bords, `HasDerivWithinAt … (Icc 0 t₀)`), de dérivée `t ↦ f(t,u(t))` continue.
Pour la stabilité, l'hypothèse `u, v ∈ C¹` est remplacée par la seule dérivabilité sur `[0,T]`
(la continuité de la dérivée n'est pas utilisée). -/
theorem th_Cauchy_Lipschitz {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn (uncurry f) (Ici 0 ×ˢ Ω))
    (hlip : ∀ T ≥ (0 : ℝ), ∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ t ∈ Icc 0 T, ∀ x ∈ K, ∀ y ∈ K,
      ‖f t x - f t y‖ ≤ C * ‖x - y‖) :
    (∀ x₀ ∈ Ω, ∃ t₀ > 0, ∃ u : ℝ → EuclideanSpace ℝ (Fin d), u 0 = x₀ ∧
      (∀ t ∈ Icc 0 t₀, u t ∈ Ω) ∧
      (∀ t ∈ Icc 0 t₀, HasDerivWithinAt u (f t (u t)) (Icc 0 t₀) t) ∧
      ContinuousOn (fun t => f t (u t)) (Icc 0 t₀)) ∧
    (∀ T > (0 : ℝ), ∀ K ⊆ Ω, IsCompact K → ∃ C : ℝ, ∀ u v : ℝ → EuclideanSpace ℝ (Fin d),
      (∀ t ∈ Icc 0 T, u t ∈ K) → (∀ t ∈ Icc 0 T, v t ∈ K) →
      (∀ t ∈ Icc 0 T, HasDerivWithinAt u (f t (u t)) (Icc 0 T) t) →
      (∀ t ∈ Icc 0 T, HasDerivWithinAt v (f t (v t)) (Icc 0 T) t) →
      ∀ t ∈ Icc 0 T, ‖u t - v t‖ ≤ Real.exp (C * t) * ‖u 0 - v 0‖) := by
  constructor
  · -- Existence
    intro x₀ hx₀
    obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
    set a : ℝ := ε / 2 with ha_def
    have ha : 0 < a := half_pos hε
    have hBΩ : closedBall x₀ a ⊆ Ω :=
      (closedBall_subset_ball (half_lt_self hε)).trans hεΩ
    obtain ⟨C, hC⟩ := hlip 1 zero_le_one (closedBall x₀ a) hBΩ (isCompact_closedBall x₀ a)
    have hcomp : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall x₀ a) :=
      isCompact_Icc.prod (isCompact_closedBall x₀ a)
    have hsub : Icc (0 : ℝ) 1 ×ˢ closedBall x₀ a ⊆ Ici 0 ×ˢ Ω :=
      prod_mono Icc_subset_Ici_self hBΩ
    obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn (hf.mono hsub)
    set Lr : ℝ := max M 0
    set L : ℝ≥0 := ⟨Lr, le_max_right _ _⟩
    set Kl : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
    set t₀ : ℝ := min 1 (a / (Lr + 1)) with ht₀_def
    have hLr : 0 ≤ Lr := le_max_right _ _
    have ht₀ : 0 < t₀ := lt_min one_pos (div_pos ha (by linarith))
    have ht₀1 : t₀ ≤ 1 := min_le_left _ _
    have hIcc : Icc 0 t₀ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right ht₀1
    set s₀ : Icc (0 : ℝ) t₀ := ⟨0, left_mem_Icc.2 ht₀.le⟩
    set aN : ℝ≥0 := ⟨a, ha.le⟩
    have hPL : IsPicardLindelof f s₀ x₀ aN 0 L Kl := by
      refine ⟨fun t ht => ?_, fun x hx => ?_, fun t ht x hx => ?_, ?_⟩
      · refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
        rw [dist_eq_norm, dist_eq_norm]
        exact (hC t (hIcc ht) x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · refine hf.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ?_
        exact hsub ⟨hIcc ht, hx⟩
      · exact (hM (t, x) ⟨hIcc ht, hx⟩).trans (le_max_left _ _)
      · have key : Lr * t₀ ≤ a :=
          calc Lr * t₀ ≤ Lr * (a / (Lr + 1)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hLr
            _ ≤ a := by
                rw [mul_div_assoc', div_le_iff₀ (by linarith)]
                nlinarith
        have hs0 : ((s₀ : ℝ)) = 0 := rfl
        simp only [hs0, sub_zero, sub_self, NNReal.coe_zero, max_eq_left ht₀.le]
        exact key
    obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL
      (mem_closedBall_self le_rfl)
    have hmem : ∀ t, α.compProj t ∈ closedBall x₀ a := fun t =>
      α.compProj_mem_closedBall hPL.mul_max_le
    have hder : ∀ t ∈ Icc 0 t₀, HasDerivWithinAt α.compProj (f t (α.compProj t))
        (Icc 0 t₀) t := by
      intro t ht
      apply ODE.hasDerivWithinAt_picard_Icc s₀.2
        hPL.continuousOn_uncurry α.continuous_compProj.continuousOn (fun t' _ => hmem t')
        x₀ ht |>.congr_of_mem _ ht
      intro t' ht'
      nth_rw 1 [← hα]
      rw [ODE.FunSpace.compProj_of_mem ht',
        ODE.FunSpace.next_apply]
    refine ⟨t₀, ht₀, α.compProj, ?_, fun t _ => hBΩ (hmem t), hder, ?_⟩
    · change α.compProj (s₀ : ℝ) = x₀
      rw [ODE.FunSpace.compProj_val]
      exact α.apply_of_zero
    · have : ContinuousOn (uncurry f ∘ fun t => (t, α.compProj t)) (Icc 0 t₀) := hf.comp
        (continuous_id.prodMk α.continuous_compProj).continuousOn
        fun t ht => ⟨(ht.1 : (0 : ℝ) ≤ t), hBΩ (hmem t)⟩
      exact this
  · -- Stabilité
    intro T hT K hKΩ hK
    obtain ⟨C, hC⟩ := hlip T hT.le K hKΩ hK
    set Kl : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
    refine ⟨max C 0, fun u v hu hv hu' hv' t ht => ?_⟩
    have hlipK : ∀ s ∈ Ico 0 T, LipschitzOnWith Kl (f s) K := fun s hs =>
      LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
        rw [dist_eq_norm, dist_eq_norm]
        exact (hC s (Ico_subset_Icc_self hs) x hx y hy).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hright : ∀ w : ℝ → EuclideanSpace ℝ (Fin d),
        (∀ s ∈ Icc 0 T, HasDerivWithinAt w (f s (w s)) (Icc 0 T) s) →
        ∀ s ∈ Ico 0 T, HasDerivWithinAt w (f s (w s)) (Ici s) s := by
      intro w hw s hs
      refine (hw s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin ?_
      exact mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc_left hs.1)
    have hcont : ∀ w : ℝ → EuclideanSpace ℝ (Fin d),
        (∀ s ∈ Icc 0 T, HasDerivWithinAt w (f s (w s)) (Icc 0 T) s) →
        ContinuousOn w (Icc 0 T) := fun w hw s hs => (hw s hs).continuousWithinAt
    have := dist_le_of_trajectories_ODE_of_mem (s := fun _ => K) (δ := dist (u 0) (v 0))
      hlipK (hcont u hu') (hright u hu') (fun s hs => hu s (Ico_subset_Icc_self hs))
      (hcont v hv') (hright v hv') (fun s hs => hv s (Ico_subset_Icc_self hs)) le_rfl t ht
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at this
    rw [mul_comm]
    exact this


private lemma sub_sq_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t - t ^ 2 ∈ Icc (0 : ℝ) (1 / 4) :=
  ⟨by nlinarith [ht.1, ht.2], by nlinarith [sq_nonneg (t - 1 / 2)]⟩

/-- **Ex. `ex:EDretard` (Équation différentielle avec retard).** Il existe une unique
`f ∈ C¹([0,1], ℝ)` telle que `f(0) = 1` et `f'(t) = f(t - t²)` pour tout `t ∈ [0,1]`.
Remarque : `f` est une fonction `ℝ → ℝ` dont seules les valeurs sur `[0,1]` comptent ; être
`C¹` solution signifie être dérivable sur `[0,1]` (au sens de `HasDerivWithinAt … (Icc 0 1)`)
de dérivée `t ↦ f(t - t²)` continue. L'unicité est établie parmi toutes les fonctions
dérivables sur `[0,1]` solutions (sans supposer la continuité de la dérivée). La preuve suit
le cours : point fixe de `A(f)(t) := 1 + ∫_0^t f(s - s²) ds`, `1/2`-lipschitzienne sur
`C⁰([0,1/2])` (`eq:EDO_retard_fixe`), puis prolongement à `[0,1]` par la même formule. -/
theorem ex_EDretard :
    ∃ f : ℝ → ℝ, f 0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt f (f (t - t ^ 2)) (Icc 0 1) t) ∧
      ContinuousOn (fun t => f (t - t ^ 2)) (Icc 0 1) ∧
      ∀ g : ℝ → ℝ, g 0 = 1 →
        (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g (t - t ^ 2)) (Icc 0 1) t) →
        EqOn g f (Icc 0 1) := by
  have h12 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, t - t ^ 2 ∈ Icc (0 : ℝ) (1 / 2) := fun t ht =>
    Icc_subset_Icc_right (by norm_num) (sub_sq_mem_Icc ht)
  -- l'espace `E := C⁰([0,1/2])` et l'application `A`
  let ext : C(Icc (0 : ℝ) (1 / 2), ℝ) → ℝ → ℝ := fun h y => h (projIcc 0 (1 / 2) h12 y)
  have hext : ∀ h, Continuous (ext h) := fun h => h.continuous.comp continuous_projIcc
  have hext_of_mem : ∀ h (y : Icc (0 : ℝ) (1 / 2)), ext h y = h y := fun h y => by
    simp [ext, projIcc_val]
  have hextc : ∀ h, Continuous fun s : ℝ => ext h (s - s ^ 2) := fun h =>
    (hext h).comp (by fun_prop)
  let F : C(Icc (0 : ℝ) (1 / 2), ℝ) → ℝ → ℝ := fun h t => 1 + ∫ s in (0)..t, ext h (s - s ^ 2)
  have hFd : ∀ h t, HasDerivAt (F h) (ext h (t - t ^ 2)) t := fun h t =>
    ((hextc h).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add 1
  have hFc : ∀ h, Continuous (F h) := fun h =>
    continuous_iff_continuousAt.2 fun t => (hFd h t).continuousAt
  let A : C(Icc (0 : ℝ) (1 / 2), ℝ) → C(Icc (0 : ℝ) (1 / 2), ℝ) := fun h =>
    ⟨fun t => F h t, (hFc h).comp continuous_subtype_val⟩
  have hA : ContractingWith (1 / 2) A := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun h g => ?_⟩
    refine (ContinuousMap.dist_le (by positivity)).2 fun t => ?_
    simp only [A, F, ContinuousMap.coe_mk, Real.dist_eq, add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub ((hextc h).intervalIntegrable _ _)
      ((hextc g).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := (t : ℝ))
      (f := fun s => ext h (s - s ^ 2) - ext g (s - s ^ 2)) (C := dist h g) fun s _ => by
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact ContinuousMap.dist_apply_le_dist _
    refine this.trans ?_
    rw [sub_zero, abs_of_nonneg t.2.1, mul_comm]
    push_cast
    exact mul_le_mul_of_nonneg_right t.2.2 dist_nonneg
  set fp := ContractingWith.fixedPoint A hA
  have hfp : A fp = fp := hA.fixedPoint_isFixedPt
  -- sur `[0,1/2]`, `ext fp` coïncide avec `F fp`
  have hfpF : ∀ y ∈ Icc (0 : ℝ) (1 / 2), ext fp y = F fp y := fun y hy => by
    rw [hext_of_mem fp ⟨y, hy⟩]
    conv_lhs => rw [← hfp]
    rfl
  -- toute solution vérifie l'équation intégrale
  have hint : ∀ g : ℝ → ℝ, g 0 = 1 →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g (g (t - t ^ 2)) (Icc 0 1) t) →
      ∀ t ∈ Icc (0 : ℝ) 1, g t = 1 + ∫ s in (0)..t, g (s - s ^ 2) := by
    intro g hg0 hg t ht
    have hgc : ContinuousOn g (Icc 0 1) := fun s hs => (hg s hs).continuousWithinAt
    have hsub : Icc 0 t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right ht.2
    have hcomp : ContinuousOn (fun s => g (s - s ^ 2)) (Icc 0 t) :=
      hgc.comp (by fun_prop) fun s hs =>
        Icc_subset_Icc_right (by norm_num) (sub_sq_mem_Icc (hsub hs))
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hgc.mono hsub)
      (fun s hs => ?_) (hcomp.intervalIntegrable_of_Icc ht.1), hg0]
    · ring
    · have hs' : s ∈ Icc (0 : ℝ) 1 := hsub (Ioo_subset_Icc_self hs)
      exact ((hg s hs').hasDerivAt (Icc_mem_nhds (hs.1) (hs.2.trans_le ht.2))).hasDerivWithinAt
  refine ⟨F fp, by simp [F], fun t ht => ?_, ?_, fun g hg0 hg t ht => ?_⟩
  · rw [← hfpF _ (hmem t ht)]
    exact (hFd fp t).hasDerivWithinAt
  · refine ((hextc fp).continuousOn).congr fun t ht => ?_
    exact (hfpF _ (hmem t ht)).symm
  · -- la restriction de `g` à `[0,1/2]` est un point fixe de `A`
    have hgc : ContinuousOn g (Icc (0 : ℝ) (1 / 2)) := fun s hs =>
      (hg s (Icc_subset_Icc_right (by norm_num) hs)).continuousWithinAt.mono
        (Icc_subset_Icc_right (by norm_num))
    set gC : C(Icc (0 : ℝ) (1 / 2), ℝ) := ⟨(Icc 0 (1 / 2)).domRestrict g, hgc.domRestrict⟩
    have hgext : ∀ y ∈ Icc (0 : ℝ) (1 / 2), ext gC y = g y := fun y hy =>
      hext_of_mem gC ⟨y, hy⟩
    have hFg : ∀ t ∈ Icc (0 : ℝ) 1, F gC t = g t := fun t ht => by
      rw [hint g hg0 hg t ht]
      simp only [F]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      exact hgext _ (hmem s (Icc_subset_Icc_right ht.2 hs))
    have hgfix : A gC = gC := ContinuousMap.ext fun y =>
      hFg y (Icc_subset_Icc_right (by norm_num) y.2)
    have hgfp : gC = fp := hA.fixedPoint_unique hgfix
    rw [← hFg t ht, hgfp]

/-- `ψ(s) = s/(1+s²)` est `1`-lipschitzienne (utilisé dans `ex:eqFunctIntegr`). -/
private lemma abs_div_one_add_sq_sub_le (a b : ℝ) :
    |a / (1 + a ^ 2) - b / (1 + b ^ 2)| ≤ |a - b| := by
  have ha : 0 < 1 + a ^ 2 := by positivity
  have hb : 0 < 1 + b ^ 2 := by positivity
  rw [div_sub_div _ _ ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb),
    div_le_iff₀ (mul_pos ha hb)]
  have h1 : a * (1 + b ^ 2) - (1 + a ^ 2) * b = (a - b) * (1 - a * b) := by ring
  rw [h1, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a * b),
    mul_pos ha hb]

/-- Projection de `ℝ` sur `[0,1]`, vue dans `ℝ`. -/
private noncomputable def P01 (y : ℝ) : ℝ := (projIcc (0 : ℝ) 1 zero_le_one y : ℝ)

private lemma continuous_P01 : Continuous P01 :=
  continuous_subtype_val.comp continuous_projIcc

private lemma P01_mem (y : ℝ) : P01 y ∈ Icc (0 : ℝ) 1 := (projIcc (0 : ℝ) 1 zero_le_one y).2

private lemma P01_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : P01 y = y := by
  simp [P01, projIcc_of_mem _ hy]

/-- **Ex. `ex:eqFunctIntegr` (Équation fonctionnelle intégrale).** Soient
`k ∈ C⁰([0,1] × [0,1], ]-1,1[)` et `φ ∈ C⁰([0,1])`. Alors il existe une unique `f ∈ C⁰([0,1])`
telle que `f(x) = ∫_0^1 k(x,y) f(y)/(1 + f(y)²) dy + φ(x)` pour tout `x ∈ [0,1]`.
Remarque : `k`, `φ`, `f` sont des fonctions sur `ℝ²` ou `ℝ` dont seules les valeurs sur
`[0,1]²` ou `[0,1]` comptent ; l'unicité s'entend sur `[0,1]` (`EqOn`). -/
theorem ex_eqFunctIntegr (k : ℝ → ℝ → ℝ) (hk : ContinuousOn (uncurry k) (Icc 0 1 ×ˢ Icc 0 1))
    (hk1 : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, k x y ∈ Ioo (-1) 1)
    (φ : ℝ → ℝ) (hφ : ContinuousOn φ (Icc 0 1)) :
    ∃ f : ℝ → ℝ, ContinuousOn f (Icc 0 1) ∧
      (∀ x ∈ Icc (0 : ℝ) 1, f x = (∫ y in (0)..1, k x y * f y / (1 + f y ^ 2)) + φ x) ∧
      ∀ g : ℝ → ℝ, ContinuousOn g (Icc 0 1) →
        (∀ x ∈ Icc (0 : ℝ) 1, g x = (∫ y in (0)..1, k x y * g y / (1 + g y ^ 2)) + φ x) →
        EqOn g f (Icc 0 1) := by
  -- extensions continues à `ℝ` et `ℝ²`
  set kk : ℝ → ℝ → ℝ := fun x y => k (P01 x) (P01 y) with hkk
  have hkkc : Continuous (uncurry kk) :=
    hk.comp_continuous ((continuous_P01.comp continuous_fst).prodMk
      (continuous_P01.comp continuous_snd)) fun p => ⟨P01_mem _, P01_mem _⟩
  set φφ : ℝ → ℝ := fun x => φ (P01 x)
  have hφφ : Continuous φφ := hφ.comp_continuous continuous_P01 P01_mem
  -- borne `K < 1` de `|k|`
  obtain ⟨p, hp, hpmax⟩ := (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).exists_isMaxOn
    ⟨(0, 0), ⟨left_mem_Icc.2 zero_le_one, left_mem_Icc.2 zero_le_one⟩⟩
    (continuous_abs.comp_continuousOn hk)
  set K : ℝ := |k p.1 p.2| with hK
  have hK1 : K < 1 := abs_lt.2 (hk1 p.1 hp.1 p.2 hp.2)
  have hK0 : 0 ≤ K := abs_nonneg _
  have hkK : ∀ x y, |kk x y| ≤ K := fun x y =>
    hpmax (a := (P01 x, P01 y)) ⟨P01_mem _, P01_mem _⟩
  -- l'espace `E := C⁰([0,1])` et l'application `A`
  let ext : C(Icc (0 : ℝ) 1, ℝ) → ℝ → ℝ := fun h y => h (projIcc 0 1 zero_le_one y)
  have hext : ∀ h, Continuous (ext h) := fun h => h.continuous.comp continuous_projIcc
  have hext_of_mem : ∀ h (y : Icc (0 : ℝ) 1), ext h y = h y := fun h y => by
    simp [ext, projIcc_val]
  let G : C(Icc (0 : ℝ) 1, ℝ) → ℝ → ℝ → ℝ := fun h x y => kk x y * ext h y / (1 + ext h y ^ 2)
  have hGc : ∀ h, Continuous (uncurry (G h)) := fun h => by
    refine Continuous.div (hkkc.mul ((hext h).comp continuous_snd)) (by fun_prop) ?_
    intro q; positivity
  let A : C(Icc (0 : ℝ) 1, ℝ) → C(Icc (0 : ℝ) 1, ℝ) := fun h =>
    ⟨fun x => (∫ y in (0)..1, G h x y) + φφ x,
      ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hGc h) 0 1).add
        hφφ).comp continuous_subtype_val⟩
  set KN : ℝ≥0 := ⟨K, hK0⟩
  have hA : ContractingWith KN A := by
    refine ⟨hK1, LipschitzWith.of_dist_le_mul fun h g => ?_⟩
    refine (ContinuousMap.dist_le (by positivity)).2 fun x => ?_
    simp only [A, ContinuousMap.coe_mk, Real.dist_eq, add_sub_add_right_eq_sub]
    rw [← intervalIntegral.integral_sub (((hGc h).uncurry_left (x : ℝ)).intervalIntegrable _ _)
      (((hGc g).uncurry_left (x : ℝ)).intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun y => G h (x : ℝ) y - G g (x : ℝ) y) (C := K * dist h g) fun y hy => by
        have hy' : y ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using hy)
        simp only [G, Real.norm_eq_abs, mul_div_assoc, ← mul_sub, abs_mul]
        refine mul_le_mul (hkK (x : ℝ) y) ?_ (abs_nonneg _) hK0
        refine (abs_div_one_add_sq_sub_le _ _).trans ?_
        rw [← Real.dist_eq, hext_of_mem h ⟨y, hy'⟩, hext_of_mem g ⟨y, hy'⟩]
        exact ContinuousMap.dist_apply_le_dist _
    exact this.trans (by simp only [sub_zero, abs_one, mul_one]; exact le_rfl)
  -- l'équation intégrale, écrite pour une fonction `g` continue sur `[0,1]`
  have hAeq : ∀ (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) (x : Icc (0 : ℝ) 1),
      A ⟨(Icc 0 1).domRestrict g, hg.domRestrict⟩ x =
        (∫ y in (0)..1, k x y * g y / (1 + g y ^ 2)) + φ x := by
    intro g hg x
    simp only [A, ContinuousMap.coe_mk, φφ, P01_of_mem x.2]
    congr 1
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le zero_le_one] at hy
    have h1 : ext ⟨(Icc 0 1).domRestrict g, hg.domRestrict⟩ y = g y := by
      exact hext_of_mem ⟨(Icc 0 1).domRestrict g, hg.domRestrict⟩ ⟨y, hy⟩
    simp only [G, kk, h1, P01_of_mem x.2, P01_of_mem hy]
  set fp := ContractingWith.fixedPoint A hA
  have hfp : A fp = fp := hA.fixedPoint_isFixedPt
  have hfpc : ContinuousOn (ext fp) (Icc 0 1) := (hext fp).continuousOn
  have hfp' : (⟨(Icc 0 1).domRestrict (ext fp), hfpc.domRestrict⟩ : C(Icc (0 : ℝ) 1, ℝ)) = fp :=
    ContinuousMap.ext fun y => hext_of_mem fp y
  refine ⟨ext fp, hfpc, fun x hx => ?_, fun g hg hgeq x hx => ?_⟩
  · rw [← hAeq _ hfpc ⟨x, hx⟩, hfp', hfp, hext_of_mem fp ⟨x, hx⟩]
  · have hgfix : A ⟨(Icc 0 1).domRestrict g, hg.domRestrict⟩ =
        ⟨(Icc 0 1).domRestrict g, hg.domRestrict⟩ :=
      ContinuousMap.ext fun y => (hAeq g hg y).trans (hgeq y y.2).symm
    have := congrArg (fun h : C(Icc (0 : ℝ) 1, ℝ) => h ⟨x, hx⟩) (hA.fixedPoint_unique hgfix)
    exact this.trans (hext_of_mem fp ⟨x, hx⟩).symm

end M1Analyse
