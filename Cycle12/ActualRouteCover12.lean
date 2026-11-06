import Cycle12.ActualRouteSelection12
import Cycle12.ActualMatchingPayment12

namespace Cycle12.Even12
open Cycle12.Global12 Cycle13 SimpleGraph Finset Real
open OAI.ErdosGallai.Scale
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
variable {V : Type} [Fintype V] [DecidableEq V]
namespace ActualFoldStage12
variable {G : SimpleGraph V} {L : EvenScaleLayers12 G} {i : ℕ}
variable (F : ActualFoldStage12 L i) (P : ∀ t,F.BatchPreparation t)
  (Q : ∀ t,F.AmbientQuotientPacking P t) (D : ∀ t,F.AmbientOutlineData P Q t)

def lowRouteEdges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i) : Set (Sym2 V) :=
  ⋃ j,(F.actualLowRoute P Q D hi r j).edgeSet

def matchingRouteEdges (hi : i≤L.stopIndex) (t : F.MatchingClassIndex) : Set (Sym2 V) :=
  ⋃ j,(F.classMatchingRoute P Q D hi t.1 t.2 j).edgeSet

def quotientRouteEdges (hi : i≤L.stopIndex) (t : F.BatchIndex) : Set (Sym2 V) :=
  ⋃ j,⋃ z,(F.actualQuotientRoute P Q D hi t j z).edgeSet

theorem actualRoutes_box_edges (hi : i≤L.stopIndex) (r : L.FoldCoreIndex i)
    (j : F.ActualCoreRequest P Q D hi r) :
    (F.actualRoutes P Q D hi r j).edgeSet=(F.boxRoute P Q D hi r.1 j.val).edgeSet :=
  (F.boxRoute_edges_at_core P Q D hi r.1 j.val j.property).symm

/-- This is equality, not only containment: every deleted route is used
by exactly one of the three intended closure families. -/
theorem all_used_routes_cover (hi : i≤L.stopIndex) :
    (⋃ r : L.FoldCoreIndex i,F.coreUsedRoutes P Q D hi r)=
      (⋃ r : L.FoldCoreIndex i,F.lowRouteEdges P Q D hi r)∪
        (⋃ t : F.MatchingClassIndex,F.matchingRouteEdges P Q D hi t)∪
          (⋃ t : F.BatchIndex,F.quotientRouteEdges P Q D hi t) := by
  apply Set.Subset.antisymm
  · intro e he
    obtain ⟨r,j,hj,he⟩ := Set.mem_iUnion.mp he
    rw [F.actualRoutes_box_edges P Q D hi r j] at he
    rcases j with ⟨j,hr⟩
    rcases j with k|k
    · change k∈Set.range (F.lowPairEmbedding P r.1) at hj
      obtain ⟨⟨t,l⟩,rfl⟩ := hj
      rw [F.boxRoute_edges_at_core P Q D hi r.1
        (.inl (F.lowPairEmbedding P r.1 ⟨t,l⟩)) (F.lowPairEmbedding_owner P r.1 ⟨t,l⟩)] at he
      apply Or.inl ∘ Or.inl
      refine Set.mem_iUnion.mpr ⟨⟨r.1,t⟩,Set.mem_iUnion.mpr ⟨l,?_⟩⟩
      rw [F.actualLowRoute_edges P Q D hi ⟨r.1,t⟩ l]
      exact he
    · rcases k with ⟨t,label,j⟩|⟨t,j,z⟩
      · exact Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨⟨r.1,t⟩,label⟩,Set.mem_iUnion.mpr ⟨j,he⟩⟩))
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨r.1,t⟩,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨z,he⟩⟩⟩)
  · rintro e ((he|he)|he)
    · obtain ⟨r,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨j,he⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨r,F.lowRoute_used P Q D hi r j he⟩
    · obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨j,he⟩ := Set.mem_iUnion.mp he
      exact F.matchingRoute_is_used P Q D hi t.1 t.2 j he
    · obtain ⟨t,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨j,he⟩ := Set.mem_iUnion.mp he
      obtain ⟨z,he⟩ := Set.mem_iUnion.mp he
      exact F.quotientRoute_is_used P Q D hi t j z he

end ActualFoldStage12
end
end Cycle12.Even12
