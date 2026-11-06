import Cycle12.FiveRingPatterns

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V} (f : Fin 5 ↪ V)
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
include hcycle

theorem five_frame_adj {i j : Fin 5} (hij : j=i+1 ∨ i=j+1) : G.Adj (f i) (f j) := by
  rcases hij with rfl | rfl
  · exact hcycle i
  · exact (hcycle j).symm

theorem five_cycle_no_consecutive_neighbors
    (hshort : Cycle13.NoCycleAtLeast G 6) {x : V} (hx : ∀ i, x≠f i)
    (i : Fin 5) (hxa : G.Adj x (f i)) (hxb : G.Adj x (f (i+1))) : False := by
  have hnot : ∀ i, f i≠x := fun i => (hx i).symm
  have hn : [x,f i,f (i+4),f (i+3),f (i+2),f (i+1)].Nodup := by
    fin_cases i <;> simp [List.nodup_cons,hx,hnot,f.injective.eq_iff]
  exact no_six_cycle_circumference_five hshort hn hxa
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide))) hxb.symm

/-- Every external vertex has one of the five diagonal pairs as its entire
neighborhood, once two cycle neighbors and exterior independence are known. -/
theorem five_cycle_external_pair
    (hshort : Cycle13.NoCycleAtLeast G 6)
    (hout : ∀ x y, (∀ i, x≠f i) → (∀ i, y≠f i) → ¬G.Adj x y)
    {x : V} (hx : ∀ i, x≠f i)
    (hnear : ∃ i j : Fin 5, i≠j ∧ G.Adj x (f i) ∧ G.Adj x (f j)) :
    ∃ k : Fin 5, ∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2) := by
  let S : Finset (Fin 5) := univ.filter (fun i => G.Adj x (f i))
  have htwo : ∃ i∈S, ∃ j∈S, i≠j := by
    obtain ⟨i,j,hij,hi,hj⟩ := hnear
    exact ⟨i,by simpa only [S,mem_filter,mem_univ,true_and] using hi,
      j,by simpa only [S,mem_filter,mem_univ,true_and] using hj,hij⟩
  have hind : ∀ i, i∈S → i+1∉S := by
    intro i hi hj
    have hi' : G.Adj x (f i) := (mem_filter.mp hi).2
    have hj' : G.Adj x (f (i+1)) := (mem_filter.mp hj).2
    exact five_cycle_no_consecutive_neighbors f hcycle hshort hx i hi' hj'
  obtain ⟨k,hk⟩ := five_ring_independent_pairs S htwo hind
  have hlabel : ∀ i, G.Adj x (f i) ↔ i=k ∨ i=k+2 := by
    intro i
    have hh : i∈S ↔ i∈({k,k+2}:Finset (Fin 5)) := by rw [hk]
    simpa only [S,mem_filter,mem_univ,true_and,mem_insert,mem_singleton] using hh
  refine ⟨k,?_⟩
  intro v
  by_cases hv : ∃ i, f i=v
  · obtain ⟨i,rfl⟩ := hv
    simpa only [f.injective.eq_iff] using hlabel i
  · have hvo : ∀ i, v≠f i := fun i he => hv ⟨i,he.symm⟩
    have hnot := hout x v hx hvo
    simp only [hnot,hvo,or_self]

/-- Disjoint diagonal attachment pairs would give an actual seven-cycle.
The external vertices are also proved distinct when that is needed. -/
theorem five_cycle_no_adjacent_pair_types
    (hshort : Cycle13.NoCycleAtLeast G 6) {x y : V}
    (hx : ∀ i, x≠f i) (hy : ∀ i, y≠f i) (i : Fin 5)
    (hxa : G.Adj x (f i)) (hxc : G.Adj x (f (i+2)))
    (hyb : G.Adj y (f (i+1))) (hyd : G.Adj y (f ((i+1)+2))) : False := by
  have hxy : x≠y := by
    intro he
    exact five_cycle_no_consecutive_neighbors f hcycle hshort hx i hxa (he ▸ hyb)
  have hnotx : ∀ i, f i≠x := fun i => (hx i).symm
  have hnoty : ∀ i, f i≠y := fun i => (hy i).symm
  have hyd' : G.Adj y (f (i+3)) := by
    convert hyd using 1
    congr 1
    fin_cases i <;> decide
  have hn : [x,f i,f (i+4),f (i+3),y,f (i+1),f (i+2)].Nodup := by
    fin_cases i <;> simp [List.nodup_cons,hx,hy,hnotx,hnoty,hxy,f.injective.eq_iff]
  exact no_seven_cycle_circumference_five hshort hn hxa
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (five_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide))) hyd'.symm hyb
    (five_frame_adj f hcycle (Or.inl (by fin_cases i <;> decide))) hxc.symm

end
end Cycle12
