import Cycle12.MatchingGroupPartition12
import Cycle12.TwoBlockPairPreparation12

namespace Cycle12
open Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000
variable {V : Type} [Fintype V] [DecidableEq V]

/-- Transfer a set of original edge indices back to the original graph. -/
def originalEdgeSet (H : SimpleGraph V) (S : Set H.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' S

theorem originalEdgeSet_card (H : SimpleGraph V) (S : Set H.edgeSet) :
    (originalEdgeSet H S).ncard=S.ncard :=
  Set.ncard_image_of_injective S Subtype.val_injective

theorem originalEdgeSet_subset (H : SimpleGraph V) (S : Set H.edgeSet) :
    originalEdgeSet H S⊆H.edgeSet := by
  rintro _ ⟨e,_,rfl⟩
  exact e.property

theorem originalEdgeSet_disjoint (H : SimpleGraph V) {S T : Set H.edgeSet}
    (hd : Disjoint S T) : Disjoint (originalEdgeSet H S) (originalEdgeSet H T) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨e,he,rfl⟩ ⟨f,hf,hef⟩
  have hh : f=e := Subtype.ext hef
  exact Set.disjoint_left.mp hd he (hh ▸ hf)

def matchingOriginalGroup (H : SimpleGraph V) (M : (⊤ : SimpleGraph H.edgeSet).Subgraph)
    (Q : ℕ) (t : Fin (Fintype.card M.edgeSet/Q+1)) : Set (Sym2 V) :=
  originalEdgeSet H (matchingEvenGroup M Q t : Set H.edgeSet)

def matchingRetainedGraph (H : SimpleGraph V) (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) :
    SimpleGraph V := H.deleteEdges (originalEdgeSet H M.verts)

theorem matchingRetainedGraph_edges (H : SimpleGraph V)
    (M : (⊤ : SimpleGraph H.edgeSet).Subgraph) :
    (matchingRetainedGraph H M).edgeSet=originalEdgeSet H M.vertsᶜ := by
  rw [matchingRetainedGraph,edgeSet_deleteEdges]
  ext e
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨⟨e,he⟩,?_,rfl⟩
    intro hm
    exact hn ⟨⟨e,he⟩,hm,rfl⟩
  · rintro ⟨e,he,rfl⟩
    refine ⟨e.property,?_⟩
    rintro ⟨f,hf,hfe⟩
    exact he ((Subtype.ext hfe : f=e) ▸ hf)

/-- The actual original edges are partitioned into at most one retained
edge and even groups of size at most 2Q. No edge multiplicity is lost
when passing between edge indices and original edges. -/
theorem original_matching_group_partition (H : SimpleGraph V) {Q : ℕ} (hQ : 0<Q) :
    ∃ M : (⊤ : SimpleGraph H.edgeSet).Subgraph, M.IsMatching ∧
      (matchingRetainedGraph H M) ≤ H ∧
      (matchingRetainedGraph H M).edgeSet.ncard ≤ 1 ∧
      (∀ t,matchingOriginalGroup H M Q t⊆H.edgeSet) ∧
      (∀ t,Disjoint (matchingOriginalGroup H M Q t) (matchingRetainedGraph H M).edgeSet) ∧
      Pairwise (fun t u => Disjoint (matchingOriginalGroup H M Q t) (matchingOriginalGroup H M Q u)) ∧
      ((⋃ t,matchingOriginalGroup H M Q t)∪(matchingRetainedGraph H M).edgeSet=H.edgeSet) ∧
      (∀ t,Even (matchingOriginalGroup H M Q t).ncard ∧
        (matchingOriginalGroup H M Q t).ncard ≤ 2*Q) ∧
      (Fintype.card (Fin (Fintype.card M.edgeSet/Q+1)):ℝ) ≤ (H.edgeSet.ncard:ℝ)/(2*Q)+1 := by
  obtain ⟨M,hM,hr,hcover,hdisj,hpairs,hgroup,hcount⟩ := finite_even_group_partition (I:=H.edgeSet) hQ
  refine ⟨M,hM,fun _ _ h => h.1,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [matchingRetainedGraph_edges,originalEdgeSet_card]
    exact hr
  · intro t
    exact originalEdgeSet_subset H _
  · intro t
    rw [matchingRetainedGraph_edges]
    apply originalEdgeSet_disjoint
    apply Set.disjoint_left.mpr
    intro e he hn
    exact Finset.disjoint_left.mp (hdisj t) he (Set.mem_toFinset.mpr hn)
  · intro t u htu
    apply originalEdgeSet_disjoint
    exact Finset.disjoint_coe.mpr (hpairs htu)
  · rw [matchingRetainedGraph_edges]
    ext e
    constructor
    · rintro (he|he)
      · obtain ⟨t,ht⟩ := Set.mem_iUnion.mp he
        exact originalEdgeSet_subset H _ ht
      · exact originalEdgeSet_subset H _ he
    · intro he
      let k : H.edgeSet := ⟨e,he⟩
      have hk : k∈univ.biUnion (matchingEvenGroup M Q)∪M.vertsᶜ.toFinset := by rw [hcover]; simp
      rcases mem_union.mp hk with hk|hk
      · obtain ⟨t,_,ht⟩ := mem_biUnion.mp hk
        exact Or.inl (Set.mem_iUnion.mpr ⟨t,⟨k,ht,rfl⟩⟩)
      · exact Or.inr ⟨k,Set.mem_toFinset.mp hk,rfl⟩
  · intro t
    simpa only [matchingOriginalGroup,originalEdgeSet_card,Set.ncard_coe_finset] using hgroup t
  · simpa only [Set.fintypeCard_eq_ncard] using hcount

end
end Cycle12
