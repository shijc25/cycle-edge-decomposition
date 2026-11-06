import OAI.Combinatorics.CycleDecomposition.Representatives

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I V : Type} [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty V]

/-- Greedy capacitated representatives with an arbitrary bounded conflict graph.
Conflict edges encode both repeated roots and paired route endpoints. -/
theorem choose_representatives_with_conflicts (A : Finset I) (K : SimpleGraph I)
    (N : I → Finset V) (k d : ℕ) (hdeg : ∀ i, K.degree i ≤ d)
    (hroom : ∀ i∈A, A.card ≤ ((N i).card-d)*k) :
    ∃ f : I → V, (∀ i∈A, f i∈N i) ∧
      (∀ i∈A, ∀ j∈A, K.Adj i j → f i≠f j) ∧
      (∀ v, (A.filter (fun i => f i=v)).card ≤ k) := by
  induction A using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance,by simp⟩
  | @insert i A hi ih =>
    obtain ⟨f,hf,hsep,hcap⟩ := ih (by
      intro j hj
      exact (Finset.card_le_card (Finset.subset_insert i A)).trans (hroom j (by simp [hj])))
    let S := (A.filter (fun j => K.Adj i j)).image f
    have hS : S.card ≤ d := by
      have hsub : A.filter (fun j => K.Adj i j) ⊆ K.neighborFinset i := by
        intro j hj
        exact (K.mem_neighborFinset i j).mpr (Finset.mem_filter.mp hj).2
      exact (Finset.card_image_le).trans ((Finset.card_le_card hsub).trans
        (by simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hdeg i))
    have hsize : (N i).card-d ≤ ((N i)\S).card := by
      have hc := Finset.card_sdiff_add_card_inter (N i) S
      have hb := Finset.card_le_card (Finset.inter_subset_right (s₁:=N i) (s₂:=S))
      omega
    have hlt : A.card < ((N i)\S).card*k := by
      have hh := hroom i (by simp)
      rw [Finset.card_insert_of_notMem hi] at hh
      have hm := Nat.mul_le_mul_right k hsize
      omega
    obtain ⟨v,hv,hload⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f:=f) hlt
    have hvN := (Finset.mem_sdiff.mp hv).1
    have hvS := (Finset.mem_sdiff.mp hv).2
    let g := Function.update f i v
    have gi : g i=v := by simp [g]
    have gold : ∀ j, j≠i → g j=f j := by intro j hj; simp [g,hj]
    refine ⟨g,?_,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [gi] using hvN
      · rw [gold j (ne_of_mem_of_not_mem hj hi)]
        exact hf j hj
    · intro j hj l hl hadj
      by_cases hj0 : j=i
      · subst j
        have hli : l≠i := fun h => K.irrefl (h ▸ hadj)
        rw [gi,gold l hli]
        intro he
        apply hvS
        exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr
          ⟨Finset.mem_of_mem_insert_of_ne hl hli,hadj⟩,he.symm⟩
      · by_cases hl0 : l=i
        · subst l
          have hjA := Finset.mem_of_mem_insert_of_ne hj hj0
          rw [gold j hj0,gi]
          intro he
          exact hvS (Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨hjA,hadj.symm⟩,he⟩)
        · rw [gold j hj0,gold l hl0]
          exact hsep j (Finset.mem_of_mem_insert_of_ne hj hj0)
            l (Finset.mem_of_mem_insert_of_ne hl hl0) hadj
    · intro w
      have hold : A.filter (fun j => g j=w)=A.filter (fun j => f j=w) := by
        apply Finset.filter_congr
        intro j hj
        rw [gold j (ne_of_mem_of_not_mem hj hi)]
      rw [Finset.filter_insert,hold]
      by_cases hvw : v=w
      · simp only [gi,hvw,ite_eq_left]
        rw [Finset.card_insert_of_notMem (fun h => hi (Finset.mem_filter.mp h).1)]
        simpa only [hvw] using Nat.succ_le_of_lt hload
      · simp only [gi,hvw,ite_false]
        exact hcap w

end
end Cycle12
