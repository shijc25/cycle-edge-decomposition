import Cycle12.ActualMatchingTeams12
import Cycle12.AlternatingMatchingClosure12
import Cycle12.RouteEmbedding12

namespace Cycle12.MatchingRequestData12
open Cycle12 Cycle13 SimpleGraph Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable {H : SimpleGraph V} {G : SimpleGraph W} {U T : Finset V}
  {M : (⊤ : SimpleGraph H.edgeSet).Subgraph} {Q : ℕ}

def embeddedPairEdges (D : MatchingRequestData12 H U T M Q) (e : V ↪ W) (j : M.edgeSet) :
    Set (Sym2 W) :=
  {s(e (D.a j.val.out.1),e (D.b j.val.out.1)),s(e (D.a j.val.out.2),e (D.b j.val.out.2))}

theorem embedded_edge (D : MatchingRequestData12 H U T M Q) (e : V ↪ W) (j : H.edgeSet) :
    s(e (D.a j),e (D.b j))=Sym2.map e j.val := by
  rw [←(D.ports j).2.2.2]
  rfl

theorem embeddedPairEdges_image (D : MatchingRequestData12 H U T M Q) (e : V ↪ W) (j : M.edgeSet) :
    D.embeddedPairEdges e j=(fun x : H.edgeSet => Sym2.map e x.val) '' (matchingPairVertices M j:Set H.edgeSet) := by
  simp only [embeddedPairEdges,matchingPairVertices,Finset.coe_insert,Finset.coe_singleton,
    Set.image_insert_eq,Set.image_singleton,D.embedded_edge e]

theorem embeddedPairEdges_disjoint (D : MatchingRequestData12 H U T M Q) (e : V ↪ W)
    (hM : M.IsMatching) : Pairwise (fun j k => Disjoint (D.embeddedPairEdges e j) (D.embeddedPairEdges e k)) := by
  intro j k hjk
  rw [D.embeddedPairEdges_image,D.embeddedPairEdges_image]
  exact disjoint_set_image _ ((Sym2.map.injective e.injective).comp Subtype.val_injective)
    (Finset.disjoint_coe.mpr (matchingPairVertices_disjoint M hM hjk))

theorem embeddedPairEdges_subset (D : MatchingRequestData12 H U T M Q) (e : V ↪ W) (j : M.edgeSet) :
    D.embeddedPairEdges e j⊆Sym2.map e '' H.edgeSet := by
  rintro _ (rfl|rfl)
  · exact ⟨j.val.out.1.val,j.val.out.1.property,(D.embedded_edge e _).symm⟩
  · exact ⟨j.val.out.2.val,j.val.out.2.property,(D.embedded_edge e _).symm⟩

theorem embeddedPairEdges_union (D : MatchingRequestData12 H U T M Q) (e : V ↪ W)
    (hM : M.IsMatching) :
    (⋃ j,D.embeddedPairEdges e j)=Sym2.map e '' originalEdgeSet H M.verts := by
  have hu : (⋃ j : M.edgeSet,(matchingPairVertices M j:Set H.edgeSet))=M.verts := by
    rw [←Set.coe_toFinset M.verts,←matchingPairVertices_union M hM]
    ext j
    simp
  simp_rw [D.embeddedPairEdges_image e]
  rw [←Set.image_iUnion,hu]
  simp only [originalEdgeSet,Set.image_image,Function.comp_def]

/-- Close the actual paired matching orientation after a common router
has produced both sides. The original unpaired representative is absent
from the resulting used edge set. -/
theorem close_embedded (D : MatchingRequestData12 H U T M Q) (e : V ↪ W)
    (hM : M.IsMatching) (hQ : 0<Q) (A B : Finset W) (hAB : Disjoint A B)
    (ha : ∀ j,e (D.a j)∈A) (hb : ∀ j,e (D.b j)∈B)
    (hHG : ∀ {x y},H.Adj x y → G.Adj (e x) (e y))
    (route : ∀ j : D.Index,G.Walk (e (D.left j)) (e (D.right j)))
    (hpath : ∀ j,(route j).IsPath)
    (hAs : ∀ j v,v∈(route (.inl j)).support → v∈A)
    (hBs : ∀ j v,v∈(route (.inr j)).support → v∈B)
    (hhard : ∀ j,Disjoint (routeInterior (route j)) (((D.teams hQ).hard j).map e))
    (hteam : ∀ j k,j≠k → (D.teams hQ).team j=(D.teams hQ).team k →
      Disjoint (routeInterior (route j)) (routeInterior (route k)))
    (hedges : Pairwise (fun j k => Disjoint (route j).edgeSet (route k).edgeSet))
    (horiginal : ∀ j,Disjoint (Sym2.map e '' H.edgeSet) (route j).edgeSet) :
    ∃ P : CyclePacking G,
      P.used=Sym2.map e '' originalEdgeSet H M.verts∪(⋃ j,(route j).edgeSet) ∧
      P.count≤Fintype.card (Fin (Fintype.card M.edgeSet/Q+1)) := by
  let a₀ := fun j : M.edgeSet => e (D.a j.val.out.1)
  let a₁ := fun j : M.edgeSet => e (D.a j.val.out.2)
  let b₀ := fun j : M.edgeSet => e (D.b j.val.out.1)
  let b₁ := fun j : M.edgeSet => e (D.b j.val.out.2)
  have hardA (j : M.edgeSet) : Disjoint (routeInterior (route (.inl j)))
      (groupPorts (demandGroup Q) a₀ a₁ (demandGroup Q j)) := by
    have hh := hhard (.inl j)
    change Disjoint _ ((groupPorts (demandGroup Q) (fun j : M.edgeSet => D.a j.val.out.1)
      (fun j => D.a j.val.out.2) (demandGroup Q j)).map e) at hh
    simpa only [a₀,a₁,groupPorts_image,Finset.map_eq_image] using hh
  have hardB (j : M.edgeSet) : Disjoint (routeInterior (route (.inr j)))
      (groupPorts (demandGroup Q) b₀ b₁ (demandGroup Q j)) := by
    have hh := hhard (.inr j)
    change Disjoint _ ((groupPorts (demandGroup Q) (fun j : M.edgeSet => D.b j.val.out.1)
      (fun j => D.b j.val.out.2) (demandGroup Q j)).map e) at hh
    simpa only [b₀,b₁,groupPorts_image,Finset.map_eq_image] using hh
  obtain ⟨P,hP,hcount⟩ := alternating_matching_group_closure A B hAB (demandGroup Q) a₀ a₁ b₀ b₁
    (fun j => hHG (D.ports j.val.out.1).2.2.1) (fun j => hHG (D.ports j.val.out.2).2.2.1)
    (fun j => ha j.val.out.1) (fun j => ha j.val.out.2)
    (fun j => (e.injective.comp D.a_injective).ne (edge_out_adj M.spanningCoe j).ne)
    (matching_pair_ports_disjoint M hM (fun j => e (D.a j)) (e.injective.comp D.a_injective))
    (matching_pair_ports_disjoint M hM (fun j => e (D.b j)) (e.injective.comp D.b_injective))
    (fun j => route (.inr j)) (fun j => route (.inl j))
    (fun j => hpath (.inr j)) (fun j => hpath (.inl j)) hBs hAs hardB hardA
    (fun j k hjk hgroup => hteam (.inr j) (.inr k) (Sum.inr_injective.ne hjk) (congrArg Sum.inr hgroup))
    (fun j k hjk hgroup => hteam (.inl j) (.inl k) (Sum.inl_injective.ne hjk) (congrArg Sum.inl hgroup))
    (fun j k hjk => hedges (Sum.inr_injective.ne hjk))
    (fun j k hjk => hedges (Sum.inl_injective.ne hjk))
    (fun j k => hedges (Sum.inr_ne_inl)) (D.embeddedPairEdges_disjoint e hM)
    (fun j k => (horiginal (.inr k)).mono (D.embeddedPairEdges_subset e j) subset_rfl)
    (fun j k => (horiginal (.inl k)).mono (D.embeddedPairEdges_subset e j) subset_rfl)
  refine ⟨P,?_,hcount⟩
  change P.used=(⋃ j,D.embeddedPairEdges e j)∪(⋃ j,(route (.inr j)).edgeSet)∪
    (⋃ j,(route (.inl j)).edgeSet) at hP
  rw [D.embeddedPairEdges_union e hM] at hP
  rw [hP]
  ext f
  simp only [Set.mem_union,Set.mem_iUnion]
  constructor
  · rintro ((h|⟨j,hj⟩)|⟨j,hj⟩)
    · exact Or.inl h
    · exact Or.inr ⟨.inr j,hj⟩
    · exact Or.inr ⟨.inl j,hj⟩
  · rintro (h|⟨j,hj⟩)
    · exact Or.inl (Or.inl h)
    · cases j with
      | inl j => exact Or.inr ⟨j,hj⟩
      | inr j => exact Or.inl (Or.inr ⟨j,hj⟩)

end
end Cycle12.MatchingRequestData12
