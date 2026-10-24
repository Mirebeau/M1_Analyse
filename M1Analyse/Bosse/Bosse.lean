/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import M1Analyse.TopologieGenerale.EspacesFonctionnels

/-!
# §A Fonctions bosse `C^∞` (`sec:bosse`)

Source : `Include/Bosse.tex` (annexe, section `sec:bosse` de `M1_Analyse.tex`).

On travaille sur `ℝ^d = EuclideanSpace ℝ (Fin d)`. Les fonctions `C^∞` sont les fonctions
`ContDiff ℝ ∞` de Mathlib ; le support `supp φ` du cours est la fermeture `tsupport φ` de
`{φ ≠ 0}` ; « `φ ∈ C^∞_c(Ω, [0,1])` » est traduit par `ContDiff ℝ ∞ φ`, `HasCompactSupport φ`,
`tsupport φ ⊆ Ω` et `φ x ∈ [0,1]` pour tout `x`. Les briques Mathlib utilisées sont
`expNegInvGlue`, `Real.smoothTransition`, `exists_contMDiffMap_zero_one_of_isClosed` et
`SmoothPartitionOfUnity`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Manifold

namespace M1Analyse

/-! ### Fonctions sur `ℝ` -/

/-- **Lemme `lem:cinfExpInv` (Prolongement lisse de la fonction nulle).** La fonction
`φ(x) = exp(-1/x)` si `x > 0`, `φ(x) = 0` sinon, est `C^∞` sur `ℝ`. (C'est la fonction
`expNegInvGlue` de Mathlib.) -/
theorem lem_cinfExpInv :
    ContDiff ℝ ∞ (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) := by
  have h : (fun x : ℝ => if 0 < x then Real.exp (-1 / x) else 0) = expNegInvGlue := by
    funext x
    by_cases hx : 0 < x
    · simp [expNegInvGlue, hx, not_le.mpr hx, neg_div, one_div]
    · simp [expNegInvGlue, hx, not_lt.mp hx]
  rw [h]
  exact expNegInvGlue.contDiff

/-- **Prop. `prop:cinfHeaviside` (Approximation de Heaviside).** Il existe `φ ∈ C^∞(ℝ)`,
croissante, positive, telle que `φ = 0` sur `]-∞, 0]` et `φ = 1` sur `[1, ∞[`.
(Mathlib : `Real.smoothTransition`.) -/
theorem prop_cinfHeaviside :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ Monotone φ ∧ (∀ x, 0 ≤ φ x) ∧
      EqOn φ 0 (Iic 0) ∧ EqOn φ 1 (Ici 1) :=
  ⟨Real.smoothTransition, Real.smoothTransition.contDiff, Real.smoothTransition.monotone,
    Real.smoothTransition.nonneg, fun _ hx => Real.smoothTransition.zero_of_nonpos hx,
    fun _ hx => Real.smoothTransition.one_of_one_le hx⟩

/-! ### Noyau de convolution -/

variable {d : ℕ}

/-- Profil radial de la preuve de `prop:cinfBosse` : `x ↦ φ_heav(2 - 3|x|)`. -/
private noncomputable def bosseProfil (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.smoothTransition (2 - 3 * ‖x‖)

private lemma bosseProfil_eq_one {x : EuclideanSpace ℝ (Fin d)} (hx : ‖x‖ ≤ 1 / 3) :
    bosseProfil x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private lemma bosseProfil_eq_zero {x : EuclideanSpace ℝ (Fin d)} (hx : 2 / 3 ≤ ‖x‖) :
    bosseProfil x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private lemma bosseProfil_contDiff : ContDiff ℝ ∞ (bosseProfil (d := d)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine contDiffAt_const (c := (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin d)) (by norm_num : (0 : ℝ) < 1 / 3)]
      with y hy
    exact bosseProfil_eq_one (mem_ball_zero_iff.mp hy).le
  · exact Real.smoothTransition.contDiffAt.comp x
      (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_norm ℝ hx)))

private lemma bosseProfil_tsupport :
    tsupport (bosseProfil (d := d)) ⊆ closedBall 0 (2 / 3) := by
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  by_contra h
  simp only [mem_closedBall, dist_zero_right, not_le] at h
  exact hx (bosseProfil_eq_zero h.le)

private lemma bosseProfil_hasCompactSupport : HasCompactSupport (bosseProfil (d := d)) :=
  (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) bosseProfil_tsupport

private lemma bosseProfil_integral_pos : 0 < ∫ x, bosseProfil (d := d) x :=
  bosseProfil_contDiff.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    bosseProfil_hasCompactSupport (fun _ => Real.smoothTransition.nonneg _)
    (x := 0) (by rw [bosseProfil_eq_one (by simp)]; norm_num)

/-- **Prop. `prop:cinfBosse` (Noyau de convolution).** Il existe `φ ∈ C^∞(ℝ^d)`, radiale,
positive, d'intégrale unité, constante et strictement positive sur `B(0,1/3)` et telle que
`supp φ ⊆ B'(0,2/3)`. On a de plus `supp φ ⊂⊂ B(0,1)`. -/
theorem prop_cinfBosse :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ ∧
      (∀ x y, ‖x‖ = ‖y‖ → φ x = φ y) ∧ (∀ x, 0 ≤ φ x) ∧ ∫ x, φ x = 1 ∧
      (∃ c, 0 < c ∧ ∀ x ∈ ball 0 (1 / 3), φ x = c) ∧ tsupport φ ⊆ closedBall 0 (2 / 3) ∧
      (HasCompactSupport φ ∧ tsupport φ ⊆ ball 0 1) := by
  set I := ∫ x, bosseProfil (d := d) x
  have hI : 0 < I := bosseProfil_integral_pos
  have hsupp :
      tsupport (fun x : EuclideanSpace ℝ (Fin d) => bosseProfil x / I) ⊆ closedBall 0 (2 / 3) :=
    (closure_mono fun x hx => (div_ne_zero_iff.mp hx).1).trans bosseProfil_tsupport
  refine ⟨fun x => bosseProfil x / I, bosseProfil_contDiff.div_const _, fun x y h => ?_,
    fun x => div_nonneg (Real.smoothTransition.nonneg _) hI.le, ?_,
    ⟨1 / I, by positivity, fun x hx => ?_⟩, hsupp,
    (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) hsupp,
    hsupp.trans (closedBall_subset_ball (by norm_num))⟩
  · simp only [bosseProfil, h]
  · rw [integral_div]
    exact div_self hI.ne'
  · change bosseProfil x / I = 1 / I
    rw [bosseProfil_eq_one (mem_ball_zero_iff.mp hx).le]

/-! ### Approximation de fonctions indicatrices -/

/-- **Prop. `prop:cinfSupport` (Approximation d'un support).** Soit `Ω ⊆ ℝ^d` ouvert et
`K ⊂⊂ Ω` compact. Alors il existe `φ ∈ C^∞_c(Ω, [0,1])` telle que `φ = 1` sur `K`.
(Preuve via `exists_contMDiffMap_zero_one_of_isClosed`, non via les boules du cours.) -/
theorem prop_cinfSupport {Ω K : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ω ∧ (∀ x, φ x ∈ Icc 0 1) ∧ EqOn φ 1 K := by
  obtain ⟨U, hUo, hKU, hUΩ, hUc⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed
    (n := (⊤ : ℕ∞)) 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) hUo.isClosed_compl hK.isClosed
    (disjoint_compl_left_iff_subset.mpr hKU)
  have hsupp : tsupport f ⊆ closure U :=
    closure_mono fun x hx => by_contra fun h => hx (hf0 h)
  exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff,
    hUc.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hUΩ, hf01, hf1⟩

/-- **Prop. `prop:cinfPartition` (Partition de l'unité).** Soit `K ⊂⊂ ℝ^d` compact et
`K ⊆ ⋃_{i} Ω_i` un recouvrement fini par des ouverts. Alors il existe `(φ_i)_i` avec
`φ_i ∈ C^∞(ℝ^d)`, `supp φ_i ⊂⊂ Ω_i` et `∑_i φ_i = 1` sur `K`. (Indices `i ∈ Fin I` au lieu de
`1 ≤ i ≤ I` ; preuve via `SmoothPartitionOfUnity.exists_isSubordinate`.) -/
theorem prop_cinfPartition {I : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : IsCompact K)
    (Ω : Fin I → Set (EuclideanSpace ℝ (Fin d))) (hΩ : ∀ i, IsOpen (Ω i))
    (hKΩ : K ⊆ ⋃ i, Ω i) :
    ∃ φ : Fin I → EuclideanSpace ℝ (Fin d) → ℝ, (∀ i, ContDiff ℝ ∞ (φ i)) ∧
      (∀ i, HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ Ω i) ∧ ∀ x ∈ K, ∑ i, φ i x = 1 := by
  obtain ⟨W, hWo, hKW, -, hWc⟩ := exists_open_between_and_isCompact_closure hK isOpen_univ
    (subset_univ K)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin d)) hK.isClosed (fun i => Ω i ∩ W)
    (fun i => (hΩ i).inter hWo) (fun x hx => by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hKΩ hx)
      exact mem_iUnion.mpr ⟨i, hi, hKW hx⟩)
  refine ⟨fun i => f i, fun i => contMDiff_iff_contDiff.mp (f i).contMDiff, fun i => ⟨?_, ?_⟩,
    fun x hx => ?_⟩
  · exact hWc.of_isClosed_subset (isClosed_tsupport _)
      ((hf i).trans (inter_subset_right.trans subset_closure))
  · exact (hf i).trans inter_subset_left
  · rw [← finsum_eq_sum_of_fintype]
    exact f.sum_eq_one hx

/-! ### Exhaustion lisse -/

/-- Décalage `K_{n-1}` d'une suite `(K_n)`, avec la convention `K_{-1} = ∅`. -/
private def decale {α : Type*} (K : ℕ → Set α) : ℕ → Set α
  | 0 => ∅
  | n + 1 => K n

/-- **Prop. `prop:cinfExhaust` (Exhaustion lisse).** Soit `Ω ⊆ ℝ^d` ouvert et `(K_n)` une suite
exhaustive de compacts de `Ω` (`prop:exhaustComp`, prédicat `EstSuiteExhaustive`) ; on pose
`K_{-1} = ∅`. Alors il existe des `φ_n ∈ C^∞_c(ℝ^d, [0,1])` telles que
`supp φ_n ⊆ int(K_{n+1}) \ K_{n-1}` et `∑_n φ_n = 1` sur `Ω`. (Le cas `n = 0`, où
`K_{-1} = ∅`, est énoncé séparément.) -/
theorem prop_cinfExhaust {Ω : Set (EuclideanSpace ℝ (Fin d))} (_hΩ : IsOpen Ω)
    {K : ℕ → Set (EuclideanSpace ℝ (Fin d))} (hK : EstSuiteExhaustive Ω K) :
    ∃ φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ ∀ x, φ n x ∈ Icc 0 1) ∧
      tsupport (φ 0) ⊆ interior (K 1) ∧
      (∀ n, tsupport (φ (n + 1)) ⊆ interior (K (n + 2)) \ K n) ∧
      ∀ x ∈ Ω, ∑' n, φ n x = 1 := by
  classical
  obtain ⟨hKc, hKU, hKi⟩ := hK
  have hmono : Monotone K := monotone_nat_of_le_succ fun n => (hKi n).trans interior_subset
  have hKΩ : ∀ n, K n ⊆ Ω := fun n => hKU ▸ subset_iUnion K n
  -- `L n` joue le rôle de `K_{n+1/2}`
  choose L hLc hKL hLK using fun n => exists_compact_between (hKc n) isOpen_interior (hKi n)
  set O : ℕ → Set (EuclideanSpace ℝ (Fin d)) := fun n => interior (K (n + 1)) \ decale K n
    with hO
  have hOo : ∀ n, IsOpen (O n) := by
    intro n
    refine isOpen_interior.sdiff ?_
    cases n with
    | zero => exact isClosed_empty
    | succ m => exact (hKc m).isClosed
  have hAc : ∀ n, IsCompact (L n \ interior (decale L n)) :=
    fun n => (hLc n).diff isOpen_interior
  have hAO : ∀ n, L n \ interior (decale L n) ⊆ O n := by
    rintro n x ⟨hxL, hx⟩
    refine ⟨hLK n hxL, fun h => hx ?_⟩
    cases n with
    | zero => exact absurd h (notMem_empty x)
    | succ m => exact hKL m h
  choose ψ hψs hψc hψt hψ01 hψ1 using fun n => prop_cinfSupport (hOo n) (hAc n) (hAO n)
  have hψ0 : ∀ n x, x ∈ decale K n → ψ n x = 0 := fun n x hx =>
    image_eq_zero_of_notMem_tsupport fun h => ((hψt n) h).2 hx
  have hψΩ : ∀ n, tsupport (ψ n) ⊆ Ω := fun n =>
    (hψt n).trans (sdiff_subset.trans (interior_subset.trans (hKΩ _)))
  -- finitude locale
  have hfin : ∀ x ∈ Ω, ∃ N, interior (K N) ∈ 𝓝 x ∧
      ∀ y ∈ interior (K N), ∀ m ∉ Finset.range (N + 1), ψ m y = 0 := by
    intro x hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp (hKU ▸ hx)
    refine ⟨N + 1, isOpen_interior.mem_nhds (hKi N hN), fun y hy m hm => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by simp at hm; omega)
    refine hψ0 _ y (hmono ?_ (interior_subset hy))
    simp at hm
    omega
  have hsumm : ∀ x, Summable fun m => ψ m x := by
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨N, hN, h⟩ := hfin x hx
      exact summable_of_ne_finset_zero (h x (mem_of_mem_nhds hN))
    · have : (fun m => ψ m x) = 0 := funext fun m =>
        image_eq_zero_of_notMem_tsupport fun h => hx (hψΩ m h)
      rw [this]
      exact summable_zero
  have hnn : ∀ m x, 0 ≤ ψ m x := fun m x => (hψ01 m x).1
  have hle : ∀ n x, ψ n x ≤ ∑' m, ψ m x := fun n x =>
    (hsumm x).le_tsum n fun j _ => hnn j x
  have hS1 : ∀ x ∈ Ω, 1 ≤ ∑' m, ψ m x := by
    intro x hx
    have hex : ∃ n, x ∈ L n := by
      obtain ⟨N, hN⟩ := mem_iUnion.mp (hKU ▸ hx)
      exact ⟨N, interior_subset (hKL N hN)⟩
    refine (hψ1 (Nat.find hex) ⟨Nat.find_spec hex, fun h => ?_⟩).symm.le.trans (hle _ x)
    cases hn : Nat.find hex with
    | zero => rw [hn] at h; exact notMem_empty x (interior_subset h)
    | succ k =>
      rw [hn] at h
      exact Nat.find_min hex (by omega : k < Nat.find hex) (interior_subset h)
  refine ⟨fun n x => ψ n x / ∑' m, ψ m x, fun n => ⟨?_, ?_, fun x => ?_⟩, ?_, fun n => ?_,
    fun x hx => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ω
    · obtain ⟨N, hN, h⟩ := hfin x hx
      have heq : ∀ y ∈ interior (K N), ∑' m, ψ m y = ∑ m ∈ Finset.range (N + 1), ψ m y :=
        fun y hy => tsum_eq_sum (h y hy)
      have hsum : ContDiffAt ℝ ∞ (fun y => ∑ m ∈ Finset.range (N + 1), ψ m y) x :=
        ContDiffAt.sum fun m _ => (hψs m).contDiffAt
      refine ((hψs n).contDiffAt.div hsum ?_).congr_of_eventuallyEq ?_
      · rw [← heq x (mem_of_mem_nhds hN)]
        exact (zero_lt_one.trans_le (hS1 x hx)).ne'
      · filter_upwards [hN] with y hy
        rw [heq y hy]
        rfl
    · have h0 : ψ n =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hψΩ n h)
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [h0] with y hy
      simp [hy]
  · exact (hψc n).mono fun x hx => (div_ne_zero_iff.mp hx).1
  · exact ⟨div_nonneg (hnn n x) (tsum_nonneg (hnn · x)),
      div_le_one_of_le₀ (hle n x) (tsum_nonneg (hnn · x))⟩
  · have h := hψt 0
    simp only [hO, decale, sdiff_empty] at h
    exact (closure_mono fun x hx => (div_ne_zero_iff.mp hx).1).trans h
  · have h := hψt (n + 1)
    simp only [hO, decale] at h
    exact (closure_mono fun x hx => (div_ne_zero_iff.mp hx).1).trans h
  · rw [tsum_div_const]
    exact div_self (zero_lt_one.trans_le (hS1 x hx)).ne'

end M1Analyse
