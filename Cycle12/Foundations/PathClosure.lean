import Cycle12.Foundations.PathPacking

namespace Cycle13
open SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] {G : SimpleGraph V}

/-- Once the return paths have been constructed, closing the original paths
produces actual edge-disjoint simple cycles with an exact edge ledger.
The existence of such return paths is deliberately not assumed automatically. -/
theorem cycle_packing_of_disjoint_returns (P : EndpointPathPacking G)
    (R : ∀ i, G.Walk (P.paths i).finish (P.paths i).start)
    (hR : ∀ i, (R i).IsPath) (hlen : ∀ i, 2 ≤ (R i).length)
    (hsep : ∀ i, (P.paths i).walk.support.tail.Disjoint (R i).support.tail)
    (hRR : Pairwise (fun i j => Disjoint (R i).edgeSet (R j).edgeSet))
    (hPR : ∀ i j, Disjoint (P.paths i).walk.edgeSet (R j).edgeSet) :
    ∃ C : CyclePacking G, C.count = P.count ∧
      C.used = P.used ∪ (⋃ i, (R i).edgeSet) ∧
      C.singles ≤ P.singles ∧ C.cost ≤ 42 * P.count + 23 * P.singles := by
  let walks := fun i => (P.paths i).walk.append (R i)
  have hc : ∀ i, (walks i).IsCycle := by
    intro i
    exact (P.paths i).isPath.isCycle_append (hR i) (hsep i) (Or.inr (hlen i))
  have hd : Pairwise (fun i j => Disjoint (walks i).edgeSet (walks j).edgeSet) := by
    intro i j hij
    simp only [walks, Walk.edgeSet_append]
    apply Set.disjoint_left.mpr
    rintro e (hi | hi) (hj | hj)
    · exact Set.disjoint_left.mp (P.disjoint hij) hi hj
    · exact Set.disjoint_left.mp (hPR i j) hi hj
    · exact Set.disjoint_left.mp (hPR j i) hj hi
    · exact Set.disjoint_left.mp (hRR hij) hi hj
  let C : CyclePacking G :=
    { count := P.count
      parts := fun i => (walks i).edgeSet
      cycles := fun i => ⟨(P.paths i).start, walks i, hc i, rfl⟩
      disjoint := hd }
  have hcount : C.count = P.count := rfl
  have hu : C.used = P.used ∪ (⋃ i, (R i).edgeSet) := by
    simp only [C, CyclePacking.used, walks, Walk.edgeSet_append, EndpointPathPacking.used,
      Set.iUnion_union_distrib]
  have hs : C.singles ≤ P.singles := by
    apply Set.ncard_le_ncard ?_ (Set.toFinite _)
    rw [CyclePacking.residue, edgeSet_deleteEdges]
    change G.edgeSet \ C.used ⊆ G.edgeSet \ P.used
    rw [hu]
    exact fun _ h => ⟨h.1, fun he => h.2 (Or.inl he)⟩
  refine ⟨C, hcount, hu, hs, ?_⟩
  unfold CyclePacking.cost
  rw [hcount]
  omega

end
end Cycle13
