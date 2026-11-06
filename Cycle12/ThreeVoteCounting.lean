import Cycle12.Foundations.FiniteProductLaw

namespace Cycle12
open Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def distinctTriples (D : Finset V) : Finset (V×V×V) :=
  (D×ˢ(D×ˢD)).filter (fun p => p.2.1≠p.1 ∧ p.2.2≠p.1 ∧ p.2.2≠p.2.1)

def tripleMajority (B : Finset V) (p : V×V×V) : Prop :=
  (p.1∈B ∧ p.2.1∈B) ∨ (p.1∈B ∧ p.2.2∈B) ∨ (p.2.1∈B ∧ p.2.2∈B)

theorem distinct_triples_card (D : Finset V) :
    (distinctTriples D).card=D.card*(D.card-1)*(D.card-2) := by
  have hsum : (distinctTriples D).card=
      ∑ x∈D, ∑ y∈D.erase x, ((D.erase x).erase y).card := by
    simp only [distinctTriples,card_filter,sum_product]
    apply sum_congr rfl
    intro x hx
    calc
      _ = ∑ y∈D, if y≠x then ((D.erase x).erase y).card else 0 := by
        apply sum_congr rfl
        intro y hy
        by_cases hxy : y=x
        · simp [hxy]
        · have he : (D.erase x).erase y=D.filter (fun z => z≠x ∧ z≠y) := by
            ext z
            simp only [mem_erase,mem_filter]
            tauto
          rw [he,card_filter]
          simp only [ne_eq,hxy,not_false_eq_true,true_and,ite_true]
      _ = _ := by
        rw [← sum_filter]
        congr 1
        ext y
        simp [and_comm]
  rw [hsum]
  have inner : ∀ x∈D, (∑ y∈D.erase x, ((D.erase x).erase y).card)=
      (D.card-1)*(D.card-2) := by
    intro x hx
    calc
      _ = ∑ _y∈D.erase x, (D.card-2) := by
        apply sum_congr rfl
        intro y hy
        rw [card_erase_of_mem hy,card_erase_of_mem hx]
        omega
      _ = _ := by simp [card_erase_of_mem hx,Nat.mul_comm]
  rw [sum_congr rfl inner,sum_const,nsmul_eq_mul]
  norm_cast
  ring

theorem triple_majority_card (D B : Finset V) (hB : B⊆D) :
    ((D×ˢ(D×ˢD)).filter (tripleMajority B)).card =
      B.card*B.card*D.card+2*(B.card*(D.card-B.card)*B.card) := by
  let E₀ := B×ˢ(B×ˢD)
  let E₁ := B×ˢ((D\B)×ˢB)
  let E₂ := (D\B)×ˢ(B×ˢB)
  have he : (D×ˢ(D×ˢD)).filter (tripleMajority B)=(E₀∪E₁)∪E₂ := by
    ext ⟨x,y,z⟩
    simp only [mem_filter,mem_product,tripleMajority,E₀,E₁,E₂,mem_union,mem_sdiff]
    constructor
    · rintro ⟨⟨hxD,hyD,hzD⟩,h⟩
      by_cases hx : x∈B <;> by_cases hy : y∈B <;> tauto
    · intro h
      rcases h with ((h | h) | h)
      · exact ⟨⟨hB h.1,hB h.2.1,h.2.2⟩,Or.inl ⟨h.1,h.2.1⟩⟩
      · exact ⟨⟨hB h.1,h.2.1.1,hB h.2.2⟩,Or.inr (Or.inl ⟨h.1,h.2.2⟩)⟩
      · exact ⟨⟨h.1.1,hB h.2.1,hB h.2.2⟩,Or.inr (Or.inr h.2)⟩
  have h01 : Disjoint E₀ E₁ := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [E₀,E₁,mem_product,mem_sdiff] at hp hq
    exact hq.2.1.2 hp.2.1
  have h02 : Disjoint E₀ E₂ := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [E₀,E₂,mem_product,mem_sdiff] at hp hq
    exact hq.1.2 hp.1
  have h12 : Disjoint E₁ E₂ := by
    apply disjoint_left.mpr
    intro p hp hq
    simp only [E₁,E₂,mem_product,mem_sdiff] at hp hq
    exact hq.1.2 hp.1
  rw [he,card_union_of_disjoint (disjoint_union_left.mpr ⟨h02,h12⟩),
    card_union_of_disjoint h01]
  simp only [E₀,E₁,E₂,card_product,card_sdiff_of_subset hB]
  ring

theorem distinct_triple_majority_card_le (D B : Finset V) (hB : B⊆D) :
    ((distinctTriples D).filter (tripleMajority B)).card ≤
      B.card*B.card*D.card+2*(B.card*(D.card-B.card)*B.card) := by
  rw [← triple_majority_card D B hB]
  exact card_le_card (filter_subset_filter _ (filter_subset _ _))

end
end Cycle12
