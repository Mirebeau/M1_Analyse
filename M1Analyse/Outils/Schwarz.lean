/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.GroupTheory.Perm.Sign

/-!
# Lemme de Schwarz itéré

Outil général, qui ne correspond à aucun énoncé du cours : si `f : E → F` est de classe `C^n`
(`E`, `F` evn réels), sa différentielle `n`-ième `D^n f(x)` est symétrique
(`iteratedFDeriv_comp_perm_of_contDiff`). Il sert notamment à identifier les dérivées partielles
`∂_α f` d'un multi-indice (cf. `M1Analyse.TopologieGenerale.EVN`).

Ce résultat est absent de Mathlib, qui ne contient que l'ordre `2`
(`ContDiffAt.isSymmSndFDerivAt`) ou le cas des fonctions analytiques
(`ContDiffAt.iteratedFDeriv_comp_perm`). On le déduit de l'ordre `2` par récurrence, les
transpositions adjacentes engendrant le groupe symétrique `𝔖_n`.
-/

namespace M1Analyse

section Schwarz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Equiv Fin

private lemma iteratedFDeriv_succ_apply_right_apply {n : ℕ} {f : E → F}
    (hf : ContDiff ℝ (n + 1) f) (x : E) (m : Fin (n + 1) → E) :
    iteratedFDeriv ℝ (n + 1) f x m =
      iteratedFDeriv ℝ n (fun y => fderiv ℝ f y (m (last n))) x (init m) := by
  rw [iteratedFDeriv_succ_apply_right]
  have h2 : (fun y => fderiv ℝ f y (m (last n))) =
      (ContinuousLinearMap.apply ℝ F (m (last n))) ∘ fderiv ℝ f := rfl
  rw [h2, (ContinuousLinearMap.apply ℝ F (m (last n))).iteratedFDeriv_comp_left
    (hf.fderiv_right (m := n) (by norm_cast)).contDiffAt le_rfl]
  rfl

private lemma iteratedFDeriv_two_succ_apply {n : ℕ} (f : E → F) (x : E)
    (m : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x m =
      iteratedFDeriv ℝ n (fderiv ℝ (fderiv ℝ f)) x (init (init m))
        (m (castSucc (last n))) (m (last (n + 1))) := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right]
  rfl

private lemma iteratedFDeriv_apply_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {g : E → G →L[ℝ] F} {x : E} (hg : ContDiffAt ℝ n g x) (u : Fin n → E) (a : G) :
    iteratedFDeriv ℝ n g x u a = iteratedFDeriv ℝ n (fun y => g y a) x u := by
  have h2 : (fun y => g y a) = (ContinuousLinearMap.apply ℝ F a) ∘ g := rfl
  rw [h2, (ContinuousLinearMap.apply ℝ F a).iteratedFDeriv_comp_left hg le_rfl]
  rfl

/-- Lemme de Schwarz itéré : si `f` est de classe `C^n` sur `E`, sa différentielle `n`-ième
`D^n f(x)` est symétrique. (Mathlib ne contient ce résultat que pour `n = 2`,
`ContDiffAt.isSymmSndFDerivAt`, ou pour `f` analytique, `ContDiffAt.iteratedFDeriv_comp_perm` ;
on l'en déduit par récurrence, les transpositions adjacentes engendrant `𝔖_n`.) -/
theorem iteratedFDeriv_comp_perm_of_contDiff : ∀ (n : ℕ) {f : E → F}, ContDiff ℝ n f →
    ∀ (x : E) (v : Fin n → E) (σ : Perm (Fin n)),
      iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v
  | 0, _, _, _, _, σ => by rw [Subsingleton.elim σ 1]; rfl
  | 1, _, _, _, _, σ => by rw [Subsingleton.elim σ 1]; rfl
  | k + 2, f, hf, x, v, σ => by
    let S : Submonoid (Perm (Fin (k + 2))) :=
      { carrier := {σ | ∀ v : Fin (k + 2) → E,
          iteratedFDeriv ℝ (k + 2) f x (v ∘ σ) = iteratedFDeriv ℝ (k + 2) f x v}
        one_mem' := fun v => rfl
        mul_mem' := fun {a b} ha hb v => by
          change iteratedFDeriv ℝ (k + 2) f x ((v ∘ a) ∘ b) = _
          rw [hb, ha] }
    have hS : S = ⊤ := by
      refine top_unique ?_
      rw [← Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩ w
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · -- transposition fixant le dernier indice : hypothèse de récurrence
        have hd : ContDiff ℝ (k + 1 : ℕ) (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
        have hg : ContDiff ℝ (k + 1 : ℕ) fun y => fderiv ℝ f y (w (last (k + 1))) :=
          (ContinuousLinearMap.apply ℝ F (w (last (k + 1)))).contDiff.comp hd
        have hf' : ContDiff ℝ ((k + 1 : ℕ) + 1) f := by exact_mod_cast hf
        rw [iteratedFDeriv_succ_apply_right_apply hf', iteratedFDeriv_succ_apply_right_apply hf']
        dsimp only; rw [Fin.succ_castSucc]
        have h1 : (w ∘ swap (castSucc j).castSucc (j.succ).castSucc) (last (k + 1)) =
            w (last (k + 1)) := by
          rw [Function.comp_apply, swap_apply_of_ne_of_ne (Fin.castSucc_lt_last _).ne'
            (Fin.castSucc_lt_last _).ne']
        have h2 : init (w ∘ swap (castSucc j).castSucc (j.succ).castSucc) =
            init w ∘ swap (castSucc j) j.succ := by
          funext l
          simp only [init, Function.comp_apply]
          rw [(Fin.castSucc_injective _).swap_apply]
        rw [h1, h2]
        exact iteratedFDeriv_comp_perm_of_contDiff (k + 1) hg x _ _
      · -- transposition des deux derniers indices : lemme de Schwarz d'ordre 2
        dsimp only
        have hsymm : ∀ y, IsSymmSndFDerivAt ℝ f y := fun y =>
          hf.contDiffAt.isSymmSndFDerivAt (by simp)
        rw [iteratedFDeriv_two_succ_apply, iteratedFDeriv_two_succ_apply]
        have h1 : init (init (w ∘ swap (castSucc (last k)) (last k).succ)) = init (init w) := by
          funext l
          simp only [init, Function.comp_apply]
          rw [swap_apply_of_ne_of_ne]
          · exact (Fin.castSucc_lt_castSucc_iff.2 (Fin.castSucc_lt_last l)).ne
          · exact (Fin.castSucc_lt_last _).ne
        rw [h1]
        simp only [Function.comp_apply, Fin.succ_last, swap_apply_left, swap_apply_right]
        have hd2 : ContDiff ℝ k (fderiv ℝ (fderiv ℝ f)) :=
          (hf.fderiv_right (m := (k + 1 : ℕ)) (by norm_cast)).fderiv_right (by norm_cast)
        rw [iteratedFDeriv_apply_eq hd2.contDiffAt, iteratedFDeriv_apply_eq hd2.contDiffAt]
        have hd2' : ContDiff ℝ k fun y => fderiv ℝ (fderiv ℝ f) y (w (last (k + 1))) :=
          hd2.clm_apply contDiff_const
        have hd2'' : ContDiff ℝ k fun y => fderiv ℝ (fderiv ℝ f) y (w (castSucc (last k))) :=
          hd2.clm_apply contDiff_const
        rw [iteratedFDeriv_apply_eq hd2'.contDiffAt, iteratedFDeriv_apply_eq hd2''.contDiffAt]
        congr 2
        funext y
        exact hsymm y _ _
    have : σ ∈ S := hS ▸ Submonoid.mem_top σ
    exact this v

end Schwarz

end M1Analyse
