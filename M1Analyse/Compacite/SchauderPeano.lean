/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import M1Analyse.Compacite.Brouwer
import M1Analyse.Compacite.Schauder
import M1Analyse.Compacite.Produits
import M1Analyse.Hilbert.Hilbert
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# §3.6 Points fixes de Brouwer (convexes) et de Schauder, théorème de Cauchy-Arzelà-Peano

Source : `Include/Compacite.tex`, corollaire suivant `th:Brouwer`, et sous-section
`subsec:Schauder`.

Ces résultats reposent sur `th_Brouwer`. Non formalisés :
`rem:SchauderEvt` (admis), `rem:preuveCauchyPeano` (mention d'une preuve alternative).
-/

open Set Metric

namespace M1Analyse

/-- Le simplexe de `ℝ^m` (coordonnées barycentriques). -/
private def schauder_simplexe (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {l | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1}

private theorem schauder_simplexe_compact (m : ℕ) : IsCompact (schauder_simplexe m) := by
  set he := (EuclideanSpace.equiv (Fin m) ℝ).toHomeomorph
  have hc : IsCompact {l : Fin m → ℝ | (∀ i, 0 ≤ l i) ∧ ∑ i, l i = 1} := by
    refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)).of_isClosed_subset
      ?_ ?_
    · rw [ofPred_and, ofPred_forall]
      exact (isClosed_iInter fun i => isClosed_le continuous_const
        (continuous_apply (A := fun _ : Fin m => ℝ) i)).inter
        (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
    · rintro l ⟨hl, hl1⟩ i -
      exact ⟨hl i, hl1 ▸ Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)⟩
  exact he.isCompact_preimage.2 hc

private theorem schauder_simplexe_convex (m : ℕ) : Convex ℝ (schauder_simplexe m) := by
  rintro l ⟨hl, hl1⟩ l' ⟨hl', hl1'⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have := hl i; have := hl' i; positivity
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hl1, hl1', hab, mul_one]

/-- **Corollaire de `th:Brouwer` (sans étiquette), convexes compacts.** Toute application
continue d'un convexe compact non vide `K` de `ℝ^d` dans lui-même admet un point fixe.
Preuve : celle du cours (homothétie ramenant `K` dans la boule unité, et projection sur `K`,
`projConvexe`, comme rétraction), appliquée directement avec `th_Brouwer`. -/
theorem corol_Brouwer_convexe {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : Convex ℝ K)
    (hKc : IsCompact K) (hKne : K.Nonempty)
    {f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hf : ContinuousOn f K) (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  -- rétraction `P` : projection sur le convexe fermé `K`
  set KC : ConvexeFerme (EuclideanSpace ℝ (Fin d)) := ⟨K, hKne, hKc.isClosed, hK⟩
  set P := projConvexe ℝ KC
  have hPK : ∀ x, P x ∈ K := fun x => (th_projConvexe (𝕜 := ℝ) KC x).1
  have hPid : ∀ x ∈ K, P x = x := fun x hx =>
    (eq_projConvexe_of_isMin (𝕜 := ℝ) KC hx (fun z _ => by simp)).symm
  have hPc : Continuous P := (th_projConvexe_lipschitz (𝕜 := ℝ) KC).continuous
  -- homothétie : `K ⊆ B'(0, R)`
  obtain ⟨R, hR0, hR⟩ : ∃ R > 0, K ⊆ closedBall 0 R := by
    obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun y => R⁻¹ • f (P (R • y))
  have hgc : ContinuousOn g (closedBall 0 1) :=
    ((hf.comp_continuous (hPc.comp (continuous_const_smul R)) fun y => hPK _).const_smul
      R⁻¹).continuousOn
  have hgB : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro y _
    have h := mem_closedBall_zero_iff.1 (hR (hfK (hPK (R • y))))
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0]
    calc R⁻¹ * ‖f (P (R • y))‖ ≤ R⁻¹ * R := by gcongr
      _ = 1 := inv_mul_cancel₀ hR0.ne'
  obtain ⟨y, -, hy⟩ := th_Brouwer hgc hgB
  have hx : f (P (R • y)) = R • y := by
    have := congrArg (R • ·) hy
    simpa [g, smul_smul, mul_inv_cancel₀ hR0.ne'] using this
  have hxK : R • y ∈ K := hx ▸ hfK (hPK _)
  exact ⟨R • y, hxK, by rw [← hPid _ hxK]; exact hx.trans (hPid _ hxK).symm⟩

private theorem schauder_approx {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {C : Set X} (hC : Convex ℝ C) (hCc : IsCompact C) (hCne : C.Nonempty) {f : X → X}
    (hf : ContinuousOn f C) (hfC : MapsTo f C C) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ C, ‖f x - x‖ ≤ ε := by
  classical
  obtain ⟨t, htC, htfin, hcov⟩ := hCc.finite_cover_balls hε
  set s := htfin.toFinset
  set m := s.card
  set xs : Fin m → X := fun i => (s.equivFin.symm i : X)
  have hxsC : ∀ i, xs i ∈ C := fun i => htC (htfin.mem_toFinset.1 (s.equivFin.symm i).2)
  have hcov' : C ⊆ ⋃ i, ball (xs i) ε := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hcov hy)
    refine mem_iUnion.2 ⟨s.equivFin ⟨z, htfin.mem_toFinset.2 hz⟩, ?_⟩
    simpa [xs] using hyz
  obtain ⟨-, -, hgε⟩ := schauderProj_spec xs C hcov'
  set w : X → Fin m → ℝ := fun y i => max 0 (ε - ‖y - xs i‖)
  have hwc : ∀ i, Continuous fun y => w y i := fun i => by fun_prop
  have hwpos : ∀ y ∈ C, 0 < ∑ i, w y i := fun y hy => schauderProj_sum_pos (hcov' hy)
  set Φ : EuclideanSpace ℝ (Fin m) → X := fun l => ∑ i, l i • xs i
  have hΦc : Continuous Φ := by fun_prop
  have hΦC : MapsTo Φ (schauder_simplexe m) C := fun l ⟨hl, hl1⟩ =>
    hC.sum_mem (fun i _ => hl i) hl1 fun i _ => hxsC i
  set F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun l =>
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => w (f (Φ l)) i / ∑ j, w (f (Φ l)) j
  have hFc : ContinuousOn F (schauder_simplexe m) := by
    have hfΦ : ContinuousOn (fun l => f (Φ l)) (schauder_simplexe m) :=
      hf.comp hΦc.continuousOn hΦC
    refine (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp_continuousOn
      (continuousOn_pi.2 fun i => ?_)
    refine ((hwc i).comp_continuousOn hfΦ).div
      (continuousOn_finsetSum _ fun j _ => (hwc j).comp_continuousOn hfΦ) fun l hl => ?_
    exact (hwpos _ (hfC (hΦC hl))).ne'
  have hFΔ : MapsTo F (schauder_simplexe m) (schauder_simplexe m) := by
    intro l hl
    have hpos := hwpos _ (hfC (hΦC hl))
    refine ⟨fun i => ?_, ?_⟩
    · change 0 ≤ w (f (Φ l)) i / ∑ j, w (f (Φ l)) j
      exact div_nonneg (le_max_left _ _) hpos.le
    · change ∑ i, w (f (Φ l)) i / ∑ j, w (f (Φ l)) j = 1
      rw [← Finset.sum_div, div_self hpos.ne']
  have hne : (schauder_simplexe m).Nonempty := by
    obtain ⟨y, hy⟩ := hCne
    obtain ⟨i, -⟩ := mem_iUnion.1 (hcov' hy)
    refine ⟨EuclideanSpace.single i 1, fun j => ?_, ?_⟩
    · simp only [PiLp.single_apply]
      split_ifs <;> norm_num
    · simp
  obtain ⟨l, hl, hFl⟩ := corol_Brouwer_convexe (schauder_simplexe_convex m)
    (schauder_simplexe_compact m) hne hFc hFΔ
  have hΦl : schauderProj ε xs (f (Φ l)) = Φ l := by
    conv_rhs => rw [← hFl]
    simp only [schauderProj, Finset.centerMass, Φ, F, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, ← div_eq_mul_inv]
    rfl
  refine ⟨Φ l, hΦC hl, ?_⟩
  have := hgε _ (hfC (hΦC hl))
  rwa [hΦl, norm_sub_rev] at this

open Filter Topology in
/-- **Th. `th:Schauder` (Point fixe de Schauder).** Soient `K` un convexe fermé non vide d'un
Banach et `f ∈ C^0(K, K)`. Si `f(K)` est d'adhérence compacte, `f` admet un point fixe.
Preuve : celle du cours (réduction à `closure (Hull f(K))`, compact par `prop:hullCompact`,
projection de Schauder `g_ε`, Brouwer, extraction). Variante : `g_ε ∘ f` est lue en
coordonnées barycentriques sur le simplexe de `ℝ^m`, au lieu de transporter `K_ε` dans un
espace euclidien. -/
theorem th_Schauder {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {K : Set X} (hK : Convex ℝ K) (hKc : IsClosed K) (hKne : K.Nonempty) {f : X → X}
    (hf : ContinuousOn f K) (hfK : MapsTo f K K) (hfc : IsCompact (closure (f '' K))) :
    ∃ x ∈ K, f x = x := by
  -- on remplace `K` par `C := closure (Hull (f K))`, convexe compact (`prop:hullCompact`)
  set C := closure (convexHull ℝ (f '' K))
  have hCc : IsCompact C := prop_hullCompact hfc
  have hCK : C ⊆ K := closure_minimal (convexHull_min hfK.image_subset hK) hKc
  have hCne : C.Nonempty :=
    (hKne.image f).mono ((subset_convexHull ℝ _).trans subset_closure)
  have hCconv : Convex ℝ C := (convex_convexHull ℝ _).closure
  have hfC : MapsTo f C C := fun x hx =>
    subset_closure (subset_convexHull ℝ _ (mem_image_of_mem f (hCK hx)))
  have hfcC : ContinuousOn f C := hf.mono hCK
  -- points fixes approchés `‖f x_n - x_n‖ ≤ 1/(n+1)`
  have hx : ∀ n : ℕ, ∃ x ∈ C, ‖f x - x‖ ≤ 1 / ((n : ℝ) + 1) := fun n =>
    schauder_approx hCconv hCc hCne hfcC hfC (by positivity)
  choose x hxC hxε using hx
  -- extraction d'une sous-suite convergente
  obtain ⟨a, haC, φ, hφ, hlim⟩ := hCc.tendsto_subseq hxC
  refine ⟨a, hCK haC, ?_⟩
  have h1 : Tendsto (fun n => f (x (φ n))) atTop (𝓝 (f a)) :=
    (hfcC a haC).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hxC _⟩)
  have h2 : Tendsto (fun n => f (x (φ n)) - x (φ n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => hxε (φ n))
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop)
  exact sub_eq_zero.1 (tendsto_nhds_unique (h1.sub hlim) h2)

open BoundedContinuousFunction in
/-- **Th. `th:CauchyPeano` (Cauchy-Arzelà-Peano).** Soient `Ω ⊂ ℝ^d` ouvert et
`f ∈ C^0(ℝ₊ × Ω, ℝ^d)`. Pour tout `x₀ ∈ Ω`, il existe `t₀ > 0` et `u ∈ C^1([0, t₀], Ω)` avec
`u(0) = x₀` et `u'(t) = f(t, u(t))` pour tout `t ∈ [0, t₀]` (même forme que
`th_Cauchy_Lipschitz`).
Preuve : celle du cours (Schauder appliqué à `F u(t) = x₀ + ∫_0^t f(s, u(s)) ds` sur
`K = C^0([0, t₀], B'(x₀, r₀))`, compacité par Arzelà–Ascoli de Mathlib). -/
theorem th_CauchyPeano {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω)
    (f : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn (Function.uncurry f) (Ici 0 ×ˢ Ω)) :
    ∀ x₀ ∈ Ω, ∃ t₀ > 0, ∃ u : ℝ → EuclideanSpace ℝ (Fin d), u 0 = x₀ ∧
      (∀ t ∈ Icc 0 t₀, u t ∈ Ω) ∧
      (∀ t ∈ Icc 0 t₀, HasDerivWithinAt u (f t (u t)) (Icc 0 t₀) t) ∧
      ContinuousOn (fun t => f t (u t)) (Icc 0 t₀) := by
  intro x₀ hx₀
  -- `B'(x₀, r₀) ⊆ Ω`, `‖f‖ ≤ C∞` sur `[0, 1] × B'(x₀, r₀)`, `t₀ C∞ ≤ r₀`
  obtain ⟨r₀, hr₀, hr₀Ω⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx₀)
  set S := Icc (0 : ℝ) 1 ×ˢ closedBall x₀ r₀
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall x₀ r₀)
  have hfS : ContinuousOn (Function.uncurry f) S :=
    hf.mono (prod_mono Icc_subset_Ici_self hr₀Ω)
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hfS
  set Cst := max M 1
  have hCst : 0 < Cst := lt_max_of_lt_right one_pos
  set t₀ := min 1 (r₀ / Cst)
  have ht₀ : 0 < t₀ := lt_min one_pos (div_pos hr₀ hCst)
  have ht₀C : Cst * t₀ ≤ r₀ := by
    calc Cst * t₀ ≤ Cst * (r₀ / Cst) := by gcongr; exact min_le_right _ _
      _ = r₀ := mul_div_cancel₀ _ hCst.ne'
  -- rétraction `ρ` sur la boule, projection `π` sur `[0, t₀]`
  set B : ConvexeFerme (EuclideanSpace ℝ (Fin d)) :=
    ⟨closedBall x₀ r₀, nonempty_closedBall.2 hr₀.le, isClosed_closedBall, convex_closedBall _ _⟩
  set ρ := projConvexe ℝ B
  have hρB : ∀ x, ρ x ∈ closedBall x₀ r₀ := fun x => (th_projConvexe (𝕜 := ℝ) B x).1
  have hρid : ∀ x ∈ closedBall x₀ r₀, ρ x = x := fun x hx =>
    (eq_projConvexe_of_isMin (𝕜 := ℝ) B hx (fun z _ => by simp)).symm
  have hρL : LipschitzWith 1 ρ := th_projConvexe_lipschitz (𝕜 := ℝ) B
  set π := projIcc 0 t₀ ht₀.le
  -- intégrande `g u s := f(s, u(s))` (prolongé hors de `[0, t₀]` et de `B'(x₀, r₀)`)
  set g : (Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) → ℝ →
      EuclideanSpace ℝ (Fin d) :=
    fun u s => f (π s) (ρ (u (π s)))
  have hgS : ∀ (u : Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) s, ((π s : ℝ), ρ (u (π s))) ∈ S :=
    fun u s =>
    ⟨⟨(π s).2.1, (π s).2.2.trans (min_le_left _ _)⟩, hρB _⟩
  have hgc : ∀ u, Continuous (g u) := fun u =>
    hfS.comp_continuous ((continuous_subtype_val.comp continuous_projIcc).prodMk
      (hρL.continuous.comp (u.continuous.comp continuous_projIcc))) (hgS u)
  have hgb : ∀ u s, ‖g u s‖ ≤ Cst := fun u s => (hM _ (hgS u s)).trans (le_max_left _ _)
  -- primitive `x₀ + ∫₀ᵗ g u`, `C∞`-lipschitzienne
  set prim : (Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) → ℝ →
      EuclideanSpace ℝ (Fin d) := fun u t => x₀ + ∫ s in (0 : ℝ)..t, g u s
  have hprim : ∀ u t t', dist (prim u t) (prim u t') ≤ Cst * dist t t' := by
    intro u t t'
    have hi : ∀ a b, IntervalIntegrable (g u) MeasureTheory.volume a b := fun a b =>
      (hgc u).intervalIntegrable a b
    rw [dist_eq_norm, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hi 0 t) (hi 0 t'), Real.dist_eq]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hgb u s
  have hprimL : ∀ u, LipschitzWith Cst.toNNReal (prim u) := fun u =>
    LipschitzWith.of_dist_le' (hprim u)
  have hprimB : ∀ u t, t ∈ Icc 0 t₀ → prim u t ∈ closedBall x₀ r₀ := by
    intro u t ht
    have := hprim u t 0
    simp only [prim, intervalIntegral.integral_same, add_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg ht.1] at this
    exact this.trans ((mul_le_mul_of_nonneg_left ht.2 hCst.le).trans ht₀C)
  -- l'opérateur `F`
  set F : (Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) →
      (Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) := fun u =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun t => prim u t, (hprimL u).continuous.comp continuous_subtype_val⟩
  have hFapp : ∀ u t, F u t = prim u t := fun u t => rfl
  set K : Set (Icc 0 t₀ →ᵇ EuclideanSpace ℝ (Fin d)) :=
    {u | ∀ t, u t ∈ closedBall x₀ r₀}
  have hKconv : Convex ℝ K := by
    intro u hu v hv a b ha hb hab t
    exact convex_closedBall x₀ r₀ (hu t) (hv t) ha hb hab
  have hKcl : IsClosed K := by
    have : K = ⋂ t, (fun u => u t) ⁻¹' closedBall x₀ r₀ := by ext u; simp [K]
    rw [this]
    exact isClosed_iInter fun t => isClosed_closedBall.preimage (continuous_eval_const t)
  have hKne : K.Nonempty :=
    ⟨BoundedContinuousFunction.const _ x₀, fun t => mem_closedBall_self hr₀.le⟩
  have hFK : MapsTo F K K := fun u _ t => hprimB u t t.2
  -- continuité (uniforme) de `F`, via l'uniforme continuité de `f` sur `S`
  have hFc : Continuous F := by
    rw [Metric.continuous_iff]
    intro u ε hε
    obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuousOn_iff.1
      (hS.uniformContinuousOn_of_continuous hfS) (ε / (2 * t₀)) (by positivity)
    refine ⟨δ, hδ, fun v hv => ?_⟩
    have hgv : ∀ s, ‖g v s - g u s‖ ≤ ε / (2 * t₀) := by
      intro s
      rw [← dist_eq_norm]
      refine (hfδ _ (hgS v s) _ (hgS u s) ?_).le
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact (hρL.dist_le_mul _ _).trans_lt (by
        rw [NNReal.coe_one, one_mul]
        exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hv)
    have hle : dist (F v) (F u) ≤ ε / 2 := by
      refine (BoundedContinuousFunction.dist_le (by positivity)).2 fun t => ?_
      rw [hFapp, hFapp, dist_eq_norm, add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub ((hgc v).intervalIntegrable _ _)
          ((hgc u).intervalIntegrable _ _)]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hgv s).trans ?_
      rw [sub_zero, abs_of_nonneg t.2.1]
      calc ε / (2 * t₀) * t ≤ ε / (2 * t₀) * t₀ := by gcongr; exact t.2.2
        _ = ε / 2 := by field_simp
    linarith
  -- compacité de `closure (F K)` (Ascoli)
  have hFcomp : IsCompact (closure (F '' K)) := by
    refine BoundedContinuousFunction.arzela_ascoli (closedBall x₀ r₀)
      (isCompact_closedBall x₀ r₀) _ ?_ ?_
    · rintro _ t ⟨u, -, rfl⟩
      exact hprimB u t t.2
    · refine (LipschitzWith.uniformEquicontinuous _ Cst.toNNReal fun v => ?_).equicontinuous
      obtain ⟨_, ⟨u, -, rfl⟩⟩ := v
      have := (hprimL u).comp (LipschitzWith.subtype_val (Icc 0 t₀))
      rw [mul_one] at this
      exact this
  -- point fixe de Schauder
  obtain ⟨u, huK, hu⟩ := th_Schauder hKconv hKcl hKne hFc.continuousOn hFK hFcomp
  have hUu : ∀ t (ht : t ∈ Icc 0 t₀), prim u t = u ⟨t, ht⟩ := fun t ht => by
    have := hFapp u ⟨t, ht⟩
    rw [hu] at this
    exact this.symm
  have hgU : ∀ t ∈ Icc 0 t₀, g u t = f t (prim u t) := by
    intro t ht
    simp only [g, π, projIcc_of_mem _ ht, hρid _ (huK _), hUu t ht]
  refine ⟨t₀, ht₀, prim u, by simp [prim], fun t ht => hr₀Ω (hprimB u t ht),
    fun t ht => ?_, (hgc u).continuousOn.congr fun t ht => (hgU t ht).symm⟩
  rw [← hgU t ht]
  exact (((hgc u).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x₀).hasDerivWithinAt

end M1Analyse

