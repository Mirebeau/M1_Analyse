/-
Copyright (c) 2026 Jean-Marie Mirebeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Marie Mirebeau
-/
import Mathlib.Topology.Order
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# §1.1.5 Continuité (`subsubsec:continuite`)

Source : `Include/TopologieGenerale.tex`, sous-sous-section `subsubsec:continuite`.

La continuité en un point et la continuité du cours sont `ContinuousAt` et `Continuous` de
Mathlib ; la semi-continuité inférieure (resp. supérieure) d'une fonction à valeurs dans
`ℝ̄ = EReal` est `LowerSemicontinuous` (resp. `UpperSemicontinuous`). Mathlib définit ces
dernières par une condition « eventually » à inégalité stricte ; les énoncés
`def_semiContinuite_*` montrent l'équivalence avec la définition du cours par les
sous-niveaux fermés.
-/

open Set Filter Topology TopologicalSpace

namespace M1Analyse

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- **Déf. `def:continuite` (Continuité en un point).** `f` est continue en `x` ssi l'image
réciproque de tout voisinage de `f(x)` est un voisinage de `x` (`eq:cont_at_x`). -/
theorem def_continuite (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ V ∈ 𝓝 (f x), f ⁻¹' V ∈ 𝓝 x :=
  continuousAt_def

/-- **Déf. `def:continuite` (Continuité sur `X`).** `f` est continue ssi elle est continue en
tout point de `X`. -/
theorem def_continuite_partout (f : X → Y) : Continuous f ↔ ∀ x, ContinuousAt f x :=
  continuous_iff_continuousAt

/-- **Éq. `eq:cont_at_x_direct`.** Reformulation par l'image directe : `f` est continue en `x`
ssi tout voisinage de `f(x)` contient l'image par `f` d'un voisinage de `x`. -/
theorem eq_cont_at_x_direct (f : X → Y) (x : X) :
    ContinuousAt f x ↔ ∀ V ∈ 𝓝 (f x), ∃ U ∈ 𝓝 x, f '' U ⊆ V := by
  rw [continuousAt_def]
  refine ⟨fun h V hV => ⟨_, h V hV, image_preimage_subset f V⟩, fun h V hV => ?_⟩
  obtain ⟨U, hU, hUV⟩ := h V hV
  exact mem_of_superset hU (image_subset_iff.mp hUV)

/-- **Déf. `def:continuite`, suite (Composition).** Si `f` est continue en `x` et `g` est
continue en `f(x)`, alors `g ∘ f` est continue en `x`. -/
theorem def_continuite_comp (f : X → Y) (g : Y → Z) (x : X)
    (hf : ContinuousAt f x) (hg : ContinuousAt g (f x)) : ContinuousAt (g ∘ f) x :=
  hg.comp hf

/-- **Prop. `prop:caract_cont` (Caractérisations de la continuité).** Pour `f : X → Y`, sont
équivalents : (i) `f` est continue en tout point ; (ii) l'image réciproque de tout ouvert est
un ouvert ; (iii) l'image réciproque de tout fermé est un fermé ;
(iv) `∀ A ⊆ X, f(Ā) ⊆ closure (f(A))`. -/
theorem prop_caract_cont (f : X → Y) :
    List.TFAE [∀ x, ContinuousAt f x,
      ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V),
      ∀ F : Set Y, IsClosed F → IsClosed (f ⁻¹' F),
      ∀ A : Set X, f '' closure A ⊆ closure (f '' A)] := by
  tfae_have 1 ↔ 2 := continuous_iff_continuousAt.symm.trans continuous_def
  tfae_have 1 ↔ 3 := continuous_iff_continuousAt.symm.trans continuous_iff_isClosed
  tfae_have 1 ↔ 4 :=
    continuous_iff_continuousAt.symm.trans continuous_iff_image_closure_subset_closure_image
  tfae_finish

/-! ### Topologie rendant continue une famille de fonctions -/

section topoFunc

variable {E : Type*} {ι : Type*} {Yi : ι → Type*} [∀ i, TopologicalSpace (Yi i)]

/-- **Rem. `rem:topoFunc` (Topologie engendrée).** Pour une famille `fᵢ : E → Yᵢ`, la
topologie engendrée par les `fᵢ⁻¹(Uᵢ)`, `Uᵢ` ouvert, rend continues toutes les `fᵢ`. -/
theorem rem_topoFunc_continue (f : ∀ i, E → Yi i) (i : ι) :
    Continuous[generateFrom {s | ∃ i, ∃ U : Set (Yi i), IsOpen U ∧ s = f i ⁻¹' U}, _] (f i) :=
  continuous_def.mpr fun U hU => GenerateOpen.basic _ ⟨i, U, hU, rfl⟩

/-- **Rem. `rem:topoFunc` (Topologie la moins fine).** Une topologie `t` sur `E` rend continues
toutes les `fᵢ` ssi elle est plus fine que la topologie engendrée par les `fᵢ⁻¹(Uᵢ)`
(dans Mathlib, `t ≤ t'` signifie que `t` est plus fine que `t'`). -/
theorem rem_topoFunc_moinsFine (f : ∀ i, E → Yi i) (t : TopologicalSpace E) :
    (∀ i, Continuous[t, _] (f i)) ↔
      t ≤ generateFrom {s | ∃ i, ∃ U : Set (Yi i), IsOpen U ∧ s = f i ⁻¹' U} := by
  rw [le_generateFrom_iff_subset_isOpen]
  constructor
  · rintro h _ ⟨i, U, hU, rfl⟩
    exact (h i).isOpen_preimage U hU
  · exact fun h i => continuous_def.mpr fun U hU => h ⟨i, U, hU, rfl⟩

/-- La topologie engendrée par les `fᵢ⁻¹(Uᵢ)` est la borne inférieure `⨅ i, induced (f i) _`
des topologies induites. -/
theorem generateFrom_preimage_eq_iInf (f : ∀ i, E → Yi i) :
    generateFrom {s | ∃ i, ∃ U : Set (Yi i), IsOpen U ∧ s = f i ⁻¹' U} =
      ⨅ i, TopologicalSpace.induced (f i) inferInstance := by
  apply le_antisymm
  · exact le_iInf fun i => continuous_iff_le_induced.mp (rem_topoFunc_continue f i)
  · rw [le_generateFrom_iff_subset_isOpen]
    rintro _ ⟨i, U, hU, rfl⟩
    have : Continuous[⨅ i, TopologicalSpace.induced (f i) inferInstance, _] (f i) :=
      continuous_iff_le_induced.mpr (iInf_le _ i)
    exact continuous_def.mp this U hU

/-- **Rem. `rem:topoFunc` (Convergence des suites).** Pour la topologie engendrée par les
`fᵢ⁻¹(Uᵢ)`, une suite `(xₙ)` converge vers `a` ssi `(fᵢ(xₙ))` converge vers `fᵢ(a)` pour tout
`i`.
Remarque : le cours dit « `(xₙ)` converge ssi `(fᵢ(xₙ))` converge pour tout `i` » ; il faut
préciser les limites (`fᵢ(a)` pour un même `a`), sinon l'énoncé est faux en général (ex. :
`X = ]0, 1]`, une seule fonction `f₁ : X → ℝ` l'injection ; `xₙ = 1/n` ne converge pas dans
`X` alors que `f₁(xₙ) → 0` dans `ℝ`). -/
theorem rem_topoFunc_suites (f : ∀ i, E → Yi i) (u : ℕ → E) (a : E) :
    Tendsto u atTop
        (@nhds E (generateFrom {s | ∃ i, ∃ U : Set (Yi i), IsOpen U ∧ s = f i ⁻¹' U}) a) ↔
      ∀ i, Tendsto (f i ∘ u) atTop (𝓝 (f i a)) := by
  rw [generateFrom_preimage_eq_iInf, nhds_iInf, tendsto_iInf]
  simp only [nhds_induced, tendsto_comap_iff]

end topoFunc

/-! ### Semi-continuité -/

/-- **Déf. `def:semiContinuite` (s.c.i.).** `f : X → ℝ̄` est semi-continue inférieurement
(`LowerSemicontinuous f` dans Mathlib) ssi `{f ≤ M}` est fermé pour tout `M ∈ ℝ̄`. -/
theorem def_semiContinuite_sci (f : X → EReal) :
    LowerSemicontinuous f ↔ ∀ M : EReal, IsClosed {x | f x ≤ M} :=
  lowerSemicontinuous_iff_isClosed_preimage

/-- **Déf. `def:semiContinuite` (s.c.s.).** `f : X → ℝ̄` est semi-continue supérieurement
(`UpperSemicontinuous f` dans Mathlib) ssi `{f ≥ M}` est fermé pour tout `M ∈ ℝ̄`. -/
theorem def_semiContinuite_scs (f : X → EReal) :
    UpperSemicontinuous f ↔ ∀ M : EReal, IsClosed {x | M ≤ f x} :=
  upperSemicontinuous_iff_isClosed_preimage

/-- **Déf. `def:semiContinuite`, suite (Opposé).** `f` est s.c.s. ssi `-f` est s.c.i. -/
theorem def_semiContinuite_neg (f : X → EReal) :
    UpperSemicontinuous f ↔ LowerSemicontinuous (fun x => -f x) := by
  rw [def_semiContinuite_scs, def_semiContinuite_sci]
  refine ⟨fun h M => ?_, fun h M => ?_⟩
  · simpa only [EReal.neg_le] using h (-M)
  · simpa only [EReal.neg_le_neg_iff] using h (-M)

/-- **Déf. `def:semiContinuite`, suite (Supremum).** Le supremum d'une famille de fonctions
s.c.i. est s.c.i. -/
theorem def_semiContinuite_iSup {ι : Sort*} (f : ι → X → EReal)
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous (fun x => ⨆ i, f i x) :=
  lowerSemicontinuous_iSup hf

/-- **Déf. `def:semiContinuite`, suite (Infimum).** L'infimum d'une famille de fonctions
s.c.s. est s.c.s. -/
theorem def_semiContinuite_iInf {ι : Sort*} (f : ι → X → EReal)
    (hf : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous (fun x => ⨅ i, f i x) :=
  upperSemicontinuous_iInf hf

/-- **Déf. `def:semiContinuite`, suite (Somme s.c.i.).** Si `f, g : X → ]-∞, ∞]` sont s.c.i.,
alors `f + g` est s.c.i. (le cours le déduit de l'égalité `eq:somme_sci`, non formalisée
ici ; la preuve Lean utilise la continuité de l'addition de `ℝ̄` hors de `(±∞, ∓∞)`). -/
theorem def_semiContinuite_add_sci (f g : X → EReal) (hf' : ∀ x, f x ≠ ⊥) (hg' : ∀ x, g x ≠ ⊥)
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x => f x + g x) :=
  hf.add' hg fun x => EReal.continuousAt_add (Or.inr (hg' x)) (Or.inl (hf' x))

/-- **Déf. `def:semiContinuite`, suite (Somme s.c.s.).** Si `f, g : X → [-∞, ∞[` sont s.c.s.,
alors `f + g` est s.c.s. -/
theorem def_semiContinuite_add_scs (f g : X → EReal) (hf' : ∀ x, f x ≠ ⊤) (hg' : ∀ x, g x ≠ ⊤)
    (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (fun x => f x + g x) :=
  hf.add' hg fun x => EReal.continuousAt_add (Or.inl (hf' x)) (Or.inr (hg' x))

/-- Version générale de `prop:surGrapheSCI`, pour `f : X → ℝ̄` quelconque (l'hypothèse
`f > -∞` du cours n'est pas nécessaire). -/
theorem lowerSemicontinuous_iff_isClosed_surGraphe (f : X → EReal) :
    LowerSemicontinuous f ↔ IsClosed {p : X × ℝ | f p.1 ≤ p.2} := by
  rw [def_semiContinuite_sci]
  constructor
  · intro h
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    rintro ⟨x, t⟩ hxt
    have hlt : ((t : ℝ) : EReal) < f x := not_le.mp hxt
    obtain ⟨α, htα, hαf⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    refine ⟨{y | f y ≤ α}ᶜ ×ˢ Iio α, ?_, (h α).isOpen_compl.prod isOpen_Iio, ?_⟩
    · rintro ⟨y, s⟩ ⟨hy, hs⟩ hys
      exact hy (le_trans hys (EReal.coe_le_coe_iff.mpr (le_of_lt hs)))
    · exact ⟨not_le.mpr hαf, EReal.coe_lt_coe_iff.mp htα⟩
  · intro hG M
    have hreal : ∀ r : ℝ, IsClosed {x | f x ≤ r} := fun r =>
      hG.preimage (continuous_id.prodMk continuous_const)
    induction M using EReal.rec with
    | bot =>
      have : {x | f x ≤ ⊥} = ⋂ r : ℝ, {x | f x ≤ r} := by
        ext x
        simp only [mem_ofPred_eq, mem_iInter]
        refine ⟨fun h r => le_trans h bot_le, fun h => ?_⟩
        by_contra hx
        obtain ⟨r, -, hr⟩ := EReal.lt_iff_exists_real_btwn.mp (bot_lt_iff_ne_bot.mpr
          (fun h' => hx (le_of_eq h')))
        exact absurd (h r) (not_le.mpr hr)
      rw [this]
      exact isClosed_iInter hreal
    | coe r => exact hreal r
    | top => simp only [le_top, ofPred_true, isClosed_univ]

/-- **Prop. `prop:surGrapheSCI`.** Soit `f : X → ]-∞, ∞]`. Alors `f` est s.c.i. ssi son
sur-graphe `𝒢 = {(x, t) ∈ X × ℝ | f(x) ≤ t}` est fermé.
Remarque : l'hypothèse `f > -∞` n'est pas utilisée
(cf. `lowerSemicontinuous_iff_isClosed_surGraphe`). -/
theorem prop_surGrapheSCI (f : X → EReal) (_hf : ∀ x, f x ≠ ⊥) :
    LowerSemicontinuous f ↔ IsClosed {p : X × ℝ | f p.1 ≤ p.2} :=
  lowerSemicontinuous_iff_isClosed_surGraphe f

end M1Analyse
