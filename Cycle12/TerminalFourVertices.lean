import Cycle12.TerminalComponents

namespace Cycle12
open SimpleGraph Finset Cycle13
noncomputable section
attribute [local instance] Classical.propDecidable

/-- All graphs on at most four vertices satisfy the terminal bound. This
also handles the K4 block without selecting a particular vertex labeling. -/
theorem terminal_affine_card_le_four {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (horder : Fintype.card V ≤ 4) :
    ∃ P : Cycle13.CyclePacking G,
      P.cost ≤ 19*(Fintype.card V-1)+6*G.edgeSet.ncard := by
  by_cases hshort : Cycle13.NoCycleAtLeast G 4
  · exact terminal_affine_no_four_cycle G hshort
  obtain ⟨u,c,hc,hlen⟩ : ∃ u, ∃ c : G.Walk u u, c.IsCycle ∧ 4 ≤ c.length := by
    by_contra hn
    apply hshort
    intro u c hc
    exact lt_of_not_ge (fun hlen => hn ⟨u,c,hc,hlen⟩)
  have hlenBound := Cycle13.cycle_length_le_order hc
  have hc4 : c.length=4 := by omega
  have hn4 : Fintype.card V=4 := by omega
  let P := Cycle13.CyclePacking.empty G
  have hPres : P.residue=G := by
    simp only [P,Cycle13.CyclePacking.empty,Cycle13.CyclePacking.residue,
      Cycle13.CyclePacking.used,Set.iUnion_of_empty,SimpleGraph.deleteEdges_empty]
  have hsub : c.edgeSet ⊆ P.residue.edgeSet := by
    rw [hPres]
    intro e he
    exact c.edges_subset_edgeSet he
  let Q := P.addCycle c.edgeSet ⟨u,c,hc,rfl⟩ hsub
  have hcount : Q.count=1 := rfl
  have hs : Q.singles+c.length=G.edgeSet.ncard := by
    have hh := P.singles_addCycle c.edgeSet ⟨u,c,hc,rfl⟩ hsub
    change Q.singles+c.edgeSet.ncard=P.singles at hh
    rw [Cycle13.cycle_edgeSet_ncard hc] at hh
    have hPs : P.singles=G.edgeSet.ncard := by
      unfold Cycle13.CyclePacking.singles
      rw [hPres]
    rw [hPs] at hh
    exact hh
  have hm := G.card_edgeFinset_le_card_choose_two
  rw [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard] at hm
  norm_num only [hn4,Nat.choose] at hm
  refine ⟨Q,?_⟩
  simp only [Cycle13.CyclePacking.cost,hcount,hn4]
  omega

end
end Cycle12
