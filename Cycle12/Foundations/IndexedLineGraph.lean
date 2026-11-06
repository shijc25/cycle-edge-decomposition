import Cycle12.Foundations.LiftingGraph

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def indexedIncident (a b : I → V) (v : V) : Finset I :=
  univ.filter (fun i => a i=v ∨ b i=v)

lemma indexedIncident_card_le (a b : I → V) (v : V) :
    (indexedIncident a b v).card ≤ Suppression.incidenceDegree a b v := by
  have hh : ∀ i, (if a i=v ∨ b i=v then (1:ℕ) else 0) ≤
      (if a i=v then 1 else 0)+(if b i=v then 1 else 0) := by
    intro i
    by_cases ha : a i=v <;> by_cases hb : b i=v <;> simp [ha,hb]
  have hs := sum_le_sum (fun i (_ : i∈(univ : Finset I)) => hh i)
  simpa only [sum_boole,Nat.cast_id,indexedIncident,Suppression.incidenceDegree] using hs

def indexedLineGraph (a b : I → V) : SimpleGraph I :=
  (liftingGraph a b).comap Sum.inr

lemma indexedLineGraph_adj (a b : I → V) (i j : I) :
    (indexedLineGraph a b).Adj i j ↔ i≠j ∧
      ∃ v, (a i=v ∨ b i=v) ∧ (a j=v ∨ b j=v) := by
  change (Sum.inr i≠Sum.inr j ∧ ∃ v, (a i=v ∨ b i=v) ∧ (a j=v ∨ b j=v)) ↔ _
  simp only [ne_eq,Sum.inr.injEq]

lemma indexedLineGraph_degree_le_two (a b : I → V)
    (hd : ∀ v, Suppression.incidenceDegree a b v ≤ 2) (i : I) :
    (indexedLineGraph a b).degree i ≤ 2 := by
  let A := (indexedIncident a b (a i)).erase i
  let B := (indexedIncident a b (b i)).erase i
  have hAi : i∈indexedIncident a b (a i) := mem_filter.mpr ⟨mem_univ _,Or.inl rfl⟩
  have hBi : i∈indexedIncident a b (b i) := mem_filter.mpr ⟨mem_univ _,Or.inr rfl⟩
  have hA : A.card ≤ 1 := by
    have hc := (indexedIncident_card_le a b (a i)).trans (hd (a i))
    have he := card_erase_add_one hAi
    change A.card+1=_ at he
    omega
  have hB : B.card ≤ 1 := by
    have hc := (indexedIncident_card_le a b (b i)).trans (hd (b i))
    have he := card_erase_add_one hBi
    change B.card+1=_ at he
    omega
  have hsub : (indexedLineGraph a b).neighborFinset i ⊆ A∪B := by
    intro j hj
    obtain ⟨hne,v,hi,hj⟩ := (indexedLineGraph_adj a b i j).mp
      ((indexedLineGraph a b).mem_neighborFinset i j |>.mp hj)
    rcases hi with ha | hb
    · exact mem_union_left B (mem_erase.mpr ⟨hne.symm,
        mem_filter.mpr ⟨mem_univ _,ha ▸ hj⟩⟩)
    · exact mem_union_right A (mem_erase.mpr ⟨hne.symm,
        mem_filter.mpr ⟨mem_univ _,hb ▸ hj⟩⟩)
  have hh := (card_le_card hsub).trans (card_union_le A B)
  rw [card_neighborFinset_eq_degree] at hh
  omega

end
end Cycle13
