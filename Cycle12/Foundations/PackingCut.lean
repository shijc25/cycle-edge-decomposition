import Cycle12.Foundations.PackingEmbedding
import Cycle12.Foundations.ReservoirLift

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

theorem induced_lifts_disjoint (G : SimpleGraph V) (S : Finset V) :
    Disjoint (reservoirLift S (G.induce (S:Set V))).edgeSet
      (reservoirLift Sᶜ (G.induce ((Sᶜ : Finset V) : Set V))).edgeSet := by
  rw [reservoirLift_induce,reservoirLift_induce]
  apply Set.disjoint_left.mpr
  intro e h₁ h₂
  induction e using Sym2.ind with
  | _ x y =>
    change G.Adj x y ∧ x∈S ∧ y∈S at h₁
    change G.Adj x y ∧ x∈Sᶜ ∧ y∈Sᶜ at h₂
    exact (mem_compl.mp h₂.2.1) h₁.2.1

theorem edges_outside_induced_lifts (G : SimpleGraph V) (S : Finset V) :
    G.edgeSet\((reservoirLift S (G.induce (S:Set V))).edgeSet∪
      (reservoirLift Sᶜ (G.induce ((Sᶜ : Finset V) : Set V))).edgeSet)=(cutGraph G S).edgeSet := by
  rw [reservoirLift_induce,reservoirLift_induce]
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    change (G.Adj x y ∧ ¬((G.Adj x y ∧ x∈S ∧ y∈S) ∨
      (G.Adj x y ∧ x∈Sᶜ ∧ y∈Sᶜ))) ↔
      G.Adj x y ∧ (x∈(S:Set V) ∧ y∉(S:Set V) ∨ x∉(S:Set V) ∧ y∈(S:Set V))
    simp only [mem_compl,mem_coe]
    tauto

/-- Cut recursion merges actual cycles on the two smaller vertex types and
charges each crossing edge exactly once as a singleton. -/
theorem exists_packing_across_cut (G : SimpleGraph V) (S : Finset V)
    (P : CyclePacking (G.induce (S:Set V))) (Q : CyclePacking (G.induce ((Sᶜ : Finset V) : Set V))) :
    ∃ C : CyclePacking G, C.count=P.count+Q.count ∧
      C.singles=P.singles+Q.singles+cutSize G S := by
  let P' := P.mapEmbedding (reservoirEmbedding S)
  let Q' := Q.mapEmbedding (reservoirEmbedding Sᶜ)
  have hP := reservoirLift_le G S (G.induce (S:Set V)) le_rfl
  have hQ := reservoirLift_le G Sᶜ (G.induce ((Sᶜ : Finset V) : Set V)) le_rfl
  have hd := induced_lifts_disjoint G S
  refine ⟨P'.combine Q' hP hQ hd,?_,?_⟩
  · erw [CyclePacking.combine_count]
    rfl
  · erw [CyclePacking.combine_singles]
    change (P.mapEmbedding (reservoirEmbedding S)).singles+
      (Q.mapEmbedding (reservoirEmbedding Sᶜ)).singles+
      (G.edgeSet\((reservoirLift S (G.induce (S:Set V))).edgeSet∪
        (reservoirLift Sᶜ (G.induce ((Sᶜ : Finset V) : Set V))).edgeSet)).ncard=_
    rw [CyclePacking.singles_mapEmbedding,CyclePacking.singles_mapEmbedding,edges_outside_induced_lifts]
    rfl

theorem induced_cut_edge_partition (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S:Set V)).edgeSet.ncard+(G.induce ((Sᶜ : Finset V) : Set V)).edgeSet.ncard+cutSize G S=
      G.edgeSet.ncard := by
  let H := reservoirLift S (G.induce (S:Set V))
  let K := reservoirLift Sᶜ (G.induce ((Sᶜ : Finset V) : Set V))
  have hd := induced_lifts_disjoint G S
  have hH : H.edgeSet⊆G.edgeSet := edgeSet_mono (reservoirLift_le G S _ le_rfl)
  have hK : K.edgeSet⊆G.edgeSet := edgeSet_mono (reservoirLift_le G Sᶜ _ le_rfl)
  have hsub : H.edgeSet∪K.edgeSet⊆G.edgeSet := Set.union_subset hH hK
  have hn := Set.ncard_sdiff_add_ncard_of_subset hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hd] at hn
  have hHi : H.edgeSet.ncard=(G.induce (S:Set V)).edgeSet.ncard := by
    dsimp [H,reservoirLift]
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding S).sym2Map.injective]
  have hKi : K.edgeSet.ncard=(G.induce ((Sᶜ : Finset V) : Set V)).edgeSet.ncard := by
    dsimp [K,reservoirLift]
    rw [SimpleGraph.edgeSet_map,Set.ncard_image_of_injective _ (reservoirEmbedding Sᶜ).sym2Map.injective]
  have hC : (G.edgeSet\(H.edgeSet∪K.edgeSet)).ncard=cutSize G S := by
    rw [edges_outside_induced_lifts]
    rfl
  rw [hHi,hKi,hC] at hn
  omega

end
end Cycle13
