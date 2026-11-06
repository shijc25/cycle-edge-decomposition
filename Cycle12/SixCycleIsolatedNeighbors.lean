import Cycle12.SixRingPatterns
import Cycle12.SixCycleFrame
import Cycle12.RobustNeighbors

namespace Cycle12
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} {G : SimpleGraph V} (f : Fin 6 ↪ V)

theorem six_frame_adj (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    {i j : Fin 6} (hij : j=i+1 ∨ i=j+1) : G.Adj (f i) (f j) := by
  rcases hij with rfl | rfl
  · exact hcycle i
  · exact (hcycle j).symm

theorem six_cycle_no_consecutive_neighbors
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hshort : Cycle13.NoCycleAtLeast G 7) {x : V} (hx : ∀ i, x≠f i)
    (i : Fin 6) (hxa : G.Adj x (f i)) (hxb : G.Adj x (f (i+1))) : False := by
  have hnot : ∀ i, f i≠x := fun i => (hx i).symm
  have hn : [x,f i,f (i+5),f (i+4),f (i+3),f (i+2),f (i+1)].Nodup := by
    fin_cases i <;> simp [List.nodup_cons,hx,hnot,f.injective.eq_iff]
  exact no_seven_cycle_circumference_six hshort hn hxa
    (six_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (six_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (six_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (six_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide)))
    (six_frame_adj f hcycle (Or.inr (by fin_cases i <;> decide))) hxb.symm

/-- An isolated exterior vertex has two distinct cycle neighbors. This
uses connectivity after vertex deletion, rather than assuming degree two. -/
theorem six_frame_isolated_two_neighbors
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    {x : V} (hx : ∀ i, x≠f i)
    (hisolated : ∀ v, (∀ i, v≠f i) → ¬G.Adj x v) :
    ∃ i j : Fin 6, i≠j ∧ G.Adj x (f i) ∧ G.Adj x (f j) := by
  have hcover : ∀ v, G.Adj x v → ∃ i, f i=v := by
    intro v hv
    by_contra hn
    exact hisolated v (fun i he => hn ⟨i,he.symm⟩) hv
  obtain ⟨v,hv,hv0⟩ := robust_neighbor_avoiding_vertex G hrobust (hx 0)
    (f.injective.ne (by decide : (1:Fin 6)≠0)) (hx 1).symm
  obtain ⟨j,rfl⟩ := hcover v hv
  obtain ⟨w,hw,hwj⟩ := robust_neighbor_avoiding_vertex G hrobust (hx j)
    hv0.symm (hx 0).symm
  obtain ⟨i,rfl⟩ := hcover w hw
  exact ⟨i,j,fun he => hwj (congrArg f he),hw,hv⟩

/-- The full neighborhood of an isolated exterior vertex is one of eleven
sets: six short pairs, three opposite pairs, or two alternating triples. -/
theorem six_frame_isolated_neighborhood
    (hcycle : ∀ i, G.Adj (f i) (f (i+1)))
    (hrobust : ∀ a, (G.induce ({a}ᶜ : Set V)).Preconnected)
    (hshort : Cycle13.NoCycleAtLeast G 7) {x : V} (hx : ∀ i, x≠f i)
    (hisolated : ∀ v, (∀ i, v≠f i) → ¬G.Adj x v) :
    ∃ k : Fin 6,
      (∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2)) ∨
      (∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+3)) ∨
      (∀ v, G.Adj x v ↔ v=f k ∨ v=f (k+2) ∨ v=f (k+4)) := by
  let S : Finset (Fin 6) := univ.filter (fun i => G.Adj x (f i))
  have htwo : ∃ i∈S, ∃ j∈S, i≠j := by
    obtain ⟨i,j,hij,hi,hj⟩ := six_frame_isolated_two_neighbors f hrobust hx hisolated
    exact ⟨i,by simpa only [S,mem_filter,mem_univ,true_and] using hi,
      j,by simpa only [S,mem_filter,mem_univ,true_and] using hj,hij⟩
  have hind : ∀ i, i∈S → i+1∉S := by
    intro i hi hj
    exact six_cycle_no_consecutive_neighbors f hcycle hshort hx i
      (mem_filter.mp hi).2 (mem_filter.mp hj).2
  have hlabel : ∀ v, G.Adj x v ↔ ∃ i∈S, f i=v := by
    intro v
    constructor
    · intro hv
      have hcover : ∃ i, f i=v := by
        by_contra hn
        exact hisolated v (fun i he => hn ⟨i,he.symm⟩) hv
      obtain ⟨i,rfl⟩ := hcover
      exact ⟨i,by simpa only [S,mem_filter,mem_univ,true_and] using hv,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact (mem_filter.mp hi).2
  obtain ⟨k,hk | hk | hk⟩ := six_ring_independent_sets S htwo hind
  · refine ⟨k,Or.inl ?_⟩
    intro v
    rw [hlabel,hk]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨i,(rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ⟨k,Or.inl rfl,rfl⟩
      · exact ⟨k+2,Or.inr rfl,rfl⟩
  · refine ⟨k,Or.inr (Or.inl ?_)⟩
    intro v
    rw [hlabel,hk]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨i,(rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr he.symm
    · rintro (rfl | rfl)
      · exact ⟨k,Or.inl rfl,rfl⟩
      · exact ⟨k+3,Or.inr rfl,rfl⟩
  · refine ⟨k,Or.inr (Or.inr ?_)⟩
    intro v
    rw [hlabel,hk]
    simp only [Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨i,(rfl | rfl | rfl),he⟩
      · exact Or.inl he.symm
      · exact Or.inr (Or.inl he.symm)
      · exact Or.inr (Or.inr he.symm)
    · rintro (rfl | rfl | rfl)
      · exact ⟨k,Or.inl rfl,rfl⟩
      · exact ⟨k+2,Or.inr (Or.inl rfl),rfl⟩
      · exact ⟨k+4,Or.inr (Or.inr rfl),rfl⟩

end
end Cycle12
