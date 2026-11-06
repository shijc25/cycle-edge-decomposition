import Cycle12.Foundations.DeficientFactorSelection
import Cycle12.Foundations.DemandPartition

/-! The actual second partial factor and protected triple for the
six-vertex terminal-pairability induction. -/
namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem seedInterior_card (w : Fin 3 ↪ V) :
    Fintype.card (SeedInterior w)+3=Fintype.card V := by
  let X := univ.image w
  have hX : X.card=3 := by rw [card_image_of_injective _ w.injective,card_univ,Fintype.card_fin]
  have hY : Fintype.card (SeedInterior w)=(univ\X).card := by
    apply Fintype.card_of_subtype
    intro v
    simp only [mem_sdiff,mem_univ,true_and,X,mem_image]
    constructor
    · intro h r he; exact h ⟨r,he.symm⟩
    · intro h ⟨r,he⟩; exact h r he.symm
  rw [hY,← hX]
  exact (card_sdiff_add_card_eq_card (subset_univ X)).trans (card_univ)

def insideFactorEmbedding (a b : I → V) (w : Fin 3 ↪ V)
    {A B : Finset I} (hdis : Disjoint A B) :
    SeedKeep (factorLeft a B) (factorLeft b B) w ↪
      SeedKeep (remainderLeft a A) (remainderLeft b A) w where
  toFun i := ⟨⟨i.val.val,fun hi => disjoint_left.mp hdis hi i.val.property⟩,i.property⟩
  inj' := by intro i j he; apply Subtype.ext; apply Subtype.ext
             exact congrArg (fun k => k.val.val) he

theorem insideFactor_degree (a b : I → V) (w : Fin 3 ↪ V)
    {A B : Finset I} (hdis : Disjoint A B) (v : SeedInterior w) :
    indexedDegreeOn (seedKeepLeft (remainderLeft a A) (remainderLeft b A) w)
      (seedKeepRight (remainderLeft a A) (remainderLeft b A) w)
      (univ.image (insideFactorEmbedding a b w hdis)) v=
      Suppression.incidenceDegree (seedKeepLeft (factorLeft a B) (factorLeft b B) w)
        (seedKeepRight (factorLeft a B) (factorLeft b B) w) v := by
  rw [indexedDegreeOn_image]
  rfl

theorem exists_second_factor (a b : I → V) (hne : ∀ i, a i≠b i)
    (w : Fin 3 ↪ V) (hsep : ∀ r s i, ¬(a i=w r ∧ b i=w s))
    {A₁ A₂ : Finset I} (hdis : Disjoint A₁ A₂)
    (hA₁ : ∀ v, indexedDegreeOn a b A₁ v=2)
    (hA₂ : ∀ v, indexedDegreeOn a b A₂ v=2) {d : ℕ}
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ d+2)
    (hspace : 2*(d+1) < Fintype.card (SeedInterior w)) :
    ∃ F : Finset (SeedKeep (remainderLeft a A₁) (remainderLeft b A₁) w),
    ∃ B : Finset (SeedInterior w),
      (∀ v, indexedDegreeOn
        (seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w)
        (seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w) F v ≤ 2) ∧
      B.card=3 ∧
      (indexedSupport (seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w)
        (seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w)).IsIndepSet B ∧
      (∀ v, indexedDegreeOn
        (seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w)
        (seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w) F v=0 → v∈B) ∧
      ((univ.filter (fun v => indexedDegreeOn
        (seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w)
        (seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w) F v ≤ 1))\B).card ≤ 3 := by
  let a' := seedKeepLeft (remainderLeft a A₁) (remainderLeft b A₁) w
  let b' := seedKeepRight (remainderLeft a A₁) (remainderLeft b A₁) w
  let F₀ := univ.image (insideFactorEmbedding a b w hdis)
  let D₂ := seedEdgeData (factorLeft a A₂) (factorLeft b A₂) w
    (fun r s i => hsep r s i.val)
  have hh := D₂.two_factor_deficiency (fun i => hne i.val)
    (fun v => (indexedDegreeOn_subtype a b A₂ v).trans (hA₂ v))
  have he : ∀ v, indexedDegreeOn a' b' F₀ v=
      Suppression.incidenceDegree (seedKeepLeft (factorLeft a A₂) (factorLeft b A₂) w)
        (seedKeepRight (factorLeft a A₂) (factorLeft b A₂) w) v :=
    fun v => insideFactor_degree a b w hdis v
  have hcap : ∀ v, indexedDegreeOn a' b' F₀ v ≤ 2 := by intro v; rw [he]; exact hh.1 v
  have hdef : (∑ v, (2-indexedDegreeOn a' b' F₀ v)) ≤ 6 := by
    simp only [he]; exact hh.2.le
  let D₁ := seedEdgeData (remainderLeft a A₁) (remainderLeft b A₁) w
    (fun r s i => hsep r s i.val)
  have hdeg : ∀ v, Suppression.incidenceDegree a' b' v ≤ d := by
    intro v
    have hkeep := D₁.keep_degree_add_star v
    have hpart := remainder_degree_add_factor a b A₁ v.val
    have hv := hd v.val
    rw [hA₁] at hpart
    change Suppression.incidenceDegree a' b' v+_= _ at hkeep
    omega
  obtain ⟨F,B,_,hF⟩ := exists_factor_protected_triple a' b'
    (fun i he => hne i.val.val (congrArg Subtype.val he)) F₀ hcap hdef hdeg hspace
  exact ⟨F,B,hF⟩

end
end Cycle13
